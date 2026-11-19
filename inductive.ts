// Inductive types: recursor derivation, positivity, and pattern rules.
import { type Global, type Globals, type Local, type RecInfo, type Sort, type Term, apply, check, close_pi, defeq, final_sort, fresh_local, open_pi, print, rec_arity, unwind } from "./kernel";
import { elab_expr } from "./elab";
import type { Expr, Statement } from "./parser";

// The largest prefix of the inductive's own binders that every constructor's
// conclusion applies unchanged, in the same position. For a simple type this
// is exactly the intuitive parameter list; for `Eq A a b` this mechanically
// also picks up `a`, which is exactly what makes the derived recursor the
// usual based (J-style) eliminator rather than one that quantifies `a` too.
export function count_core_params(ind_ty: Term, ctor_tys: Term[]): number {
	const { locals: all_ind_locals } = open_pi(ind_ty, Infinity);
	let limit = all_ind_locals.length;
	for (const ct of ctor_tys) {
		limit = Math.min(limit, open_pi(ct, Infinity).locals.length);
	}
	for (let k = limit; k > 0; k--) {
		const params = all_ind_locals.slice(0, k);
		const ok = ctor_tys.every((ct) => {
			const { body } = open_pi(ct, Infinity, params);
			const { args } = unwind(body);
			return args.length >= k && params.every((p, i) => args[i] === p);
		});
		if (ok) return k;
	}
	return 0;
}

export function derive_recursor_type(
	ind_name: string,
	ind_ty: Term,
	ctor_names: string[],
	ctor_tys: Term[],
	num_params: number,
	num_indices: number,
	motive_sort: Sort,
): Term {
	const { locals: param_locals, body: after_params } = open_pi(
		ind_ty,
		num_params,
	);
	const { locals: index_locals } = open_pi(after_params, num_indices);

	const target_ty = apply({ k: "global", name: ind_name }, [
		...param_locals,
		...index_locals,
	]);
	const target_local = fresh_local(target_ty);
	const motive_ty = close_pi(
		[...index_locals, target_local],
		{ k: "sort", s: motive_sort },
	);
	const motive_local = fresh_local(motive_ty);

	const minor_locals = ctor_names.map((cname, i) => {
		const ctor_ty = ctor_tys[i]!;
		const { locals: ctor_locals, body: ctor_concl } = open_pi(
			ctor_ty,
			Infinity,
			param_locals,
		);
		const field_locals = ctor_locals.slice(num_params);
		const { args: concl_args } = unwind(ctor_concl);
		const ctor_indices = concl_args.slice(num_params);

		const ih_locals: Term[] = [];
		for (const f of field_locals) {
			const fl = f as Local;
			const { head: fh, args: fargs } = unwind(fl.ty);
			if (fh.k === "global" && fh.name === ind_name) {
				const f_indices = fargs.slice(num_params);
				ih_locals.push(
					fresh_local(apply(motive_local, [...f_indices, f])),
				);
			}
		}

		const minor_concl = apply(motive_local, [
			...ctor_indices,
			apply({ k: "global", name: cname }, [...param_locals, ...field_locals]),
		]);
		return fresh_local(close_pi([...field_locals, ...ih_locals], minor_concl));
	});

	const tail_concl = apply(motive_local, [...index_locals, target_local]);
	const tail = close_pi([...index_locals, target_local], tail_concl);
	const with_minors = close_pi(minor_locals, tail);
	const with_motive = close_pi([motive_local], with_minors);
	return close_pi(param_locals, with_motive);
}

export function derive_and_validate_recursor(
	globals: Globals,
	ind_name: string,
	ind: Global,
	declared_ty: Term,
): RecInfo {
	const ctor_names = ind.ctors ?? [];
	const ctor_tys = ctor_names.map((c) => globals.get(c)!.ty);
	const num_params = ind.num_params ?? (ind.num_params = count_core_params(ind.ty, ctor_tys));
	const { locals: all_ind_locals } = open_pi(ind.ty, Infinity);
	const num_indices = all_ind_locals.length - num_params;
	const ind_final_sort = final_sort(ind.ty);

	const { locals: head_locals } = open_pi(declared_ty, num_params + 1);
	if (head_locals.length !== num_params + 1) {
		throw new Error(`${ind_name}'s recursor does not have a motive`);
	}
	const motive_local = head_locals[num_params] as Local;
	const motive_sort = final_sort(motive_local.ty);

	if (ind_final_sort === 0 && ctor_names.length > 1 && motive_sort !== 0) {
		throw new Error(`a Prop with more than one constructor may only eliminate into Prop`);
	}

	const canonical = derive_recursor_type(
		ind_name,
		ind.ty,
		ctor_names,
		ctor_tys,
		num_params,
		num_indices,
		motive_sort,
	);
	if (!defeq(globals, canonical, declared_ty)) {
		throw new Error(`${ind_name}'s recursor does not match the derived recursor`);
	}

	return {
		ind: ind_name,
		num_params,
		num_indices,
		ctor_order: ctor_names.slice(),
		rules: new Map(),
		rule_counts: new Map(),
	};
}

// ---------------------------------------------------------------------------
// Statements
// ---------------------------------------------------------------------------

export function spine(expr: Expr): { head: string; args: Expr[] } {
	const args: Expr[] = [];
	let cur = expr;
	while (cur.type === "application") {
		args.push(cur.value);
		cur = cur.fun;
	}
	args.reverse();
	if (cur.type !== "ident") throw new Error(`pattern head is not an identifier`);
	return { head: cur.ident, args };
}

export function occurs_in(name: string, t: Term): boolean {
	switch (t.k) {
		case "global":
			return t.name === name;
		case "app":
			return occurs_in(name, t.fn) || occurs_in(name, t.arg);
		case "pi":
		case "lam":
			return occurs_in(name, t.dom) || occurs_in(name, t.body);
		case "local":
			return occurs_in(name, t.ty);
		default:
			return false;
	}
}

// A constructor argument may mention the type being declared only strictly
// positively: either it is `ind_name ...` itself (whose own arguments then
// may not mention ind_name again - no nested self-application), or a
// function *into* one, whose domain never mentions ind_name at all.
// Without this, an @intro like
//
//   Bad.intro : (Bad -> Bad) -> Bad;
//
// would type-check, and hand every declaration in the language the same
// unsoundness a raw, unchecked axiom would: Bad would be inhabited (by
// applying Bad.intro to itself) with no way for @rec to ever catch it,
// which is exactly what marking a declaration @inductive is supposed to
// rule out instead of merely assuming.
export function check_strictly_positive(ind_name: string, arg: Term): void {
	if (!occurs_in(ind_name, arg)) return;
	if (arg.k === "pi") {
		if (occurs_in(ind_name, arg.dom)) {
			throw new Error(
				`${ind_name} appears to the left of an arrow in a constructor argument, which is not strictly positive`,
			);
		}
		check_strictly_positive(ind_name, arg.body);
		return;
	}
	const { head, args } = unwind(arg);
	if (head.k === "global" && head.name === ind_name) {
		for (const a of args) {
			if (occurs_in(ind_name, a)) {
				throw new Error(`${ind_name} appears inside its own arguments, which is not strictly positive`);
			}
		}
		return;
	}
	throw new Error(
		`${ind_name} appears in a constructor argument in a position that is not strictly positive`,
	);
}

// Walks a constructor's own leading binders (not the final conclusion the
// loop stops at, which is `ind_name` itself and is not an argument).
export function check_ctor_positivity(ind_name: string, ty: Term): void {
	let cur = ty;
	while (cur.k === "pi") {
		check_strictly_positive(ind_name, cur.dom);
		cur = cur.body;
	}
}

// Whether a definition, followed through every global it mentions, reaches
// `name`. Only definitions are followed: an axiom or constructor has no body
// to hide a recursor call in.
export function reaches_global(
	globals: Globals,
	t: Term,
	name: string,
	seen: Set<string>,
): boolean {
	switch (t.k) {
		case "global": {
			if (t.name === name) return true;
			if (seen.has(t.name)) return false;
			seen.add(t.name);
			const def = globals.get(t.name)?.def;
			return def ? reaches_global(globals, def, name, seen) : false;
		}
		case "app":
			return (
				reaches_global(globals, t.fn, name, seen) ||
				reaches_global(globals, t.arg, name, seen)
			);
		case "pi":
		case "lam":
			return (
				reaches_global(globals, t.dom, name, seen) ||
				reaches_global(globals, t.body, name, seen)
			);
		case "local":
			return reaches_global(globals, t.ty, name, seen);
		default:
			return false;
	}
}

// An iota rule may only recurse structurally: its body may apply its own
// recursor only to one of the constructor's fields, which is strictly smaller
// than the term being matched. Otherwise a rule like
//   U.rec motive c U.mk := U.rec motive c U.mk
// type-checks (the body has the right type) and sends reduction, and so the
// checker, into an infinite loop.
export function check_structural(
	globals: Globals,
	rec_name: string,
	arity: number,
	fields: Term[],
	root: Term,
): void {
	const field_ids = new Set(fields.map((f) => (f as Local).id));
	const bad = () =>
		new Error(
			`${rec_name}'s rule may only apply ${rec_name} to one of the constructor's own fields, which is the only way to recurse structurally`,
		);
	const walk = (t: Term): void => {
		switch (t.k) {
			case "app": {
				const { head, args } = unwind(t);
				if (head.k === "global" && head.name === rec_name) {
					const target = args[arity - 1];
					if (!target || target.k !== "local" || !field_ids.has(target.id)) {
						throw bad();
					}
				} else {
					walk(head);
				}
				args.forEach(walk);
				return;
			}
			case "global":
				if (reaches_global(globals, t, rec_name, new Set())) throw bad();
				return;
			case "pi":
			case "lam":
				walk(t.dom);
				walk(t.body);
				return;
			case "local":
				walk(t.ty);
				return;
		}
	};
	walk(root);
}

export function check_iota_rule(globals: Globals, stmt: Statement): void {
	const { head, args: pat_args } = spine(stmt.pat);

	if (stmt.directives.length !== 1 || stmt.directives[0]!.name !== "iota") {
		if (stmt.directives.some((d) => d.name !== "iota")) {
			throw new Error(`a rule may only be marked @iota`);
		}
		if (stmt.directives.length === 0) {
			throw new Error(`@iota needs the type the rule matches on`);
		}
		throw new Error(`a rule gets exactly one @iota marker`);
	}
	const ind_name = stmt.directives[0]!.arg;
	if (ind_name === null) {
		throw new Error(`@iota needs the type the rule matches on`);
	}

	const rec = globals.get(head);
	if (!rec || !rec.rec_info || rec.rec_info.ind !== ind_name) {
		throw new Error(`'${head}' is not the recursor for ${ind_name}`);
	}
	const info = rec.rec_info;

	const prefix_len = info.num_params + 1 + info.ctor_order.length;
	const expected_arity = prefix_len + info.num_indices + 1;
	if (pat_args.length !== expected_arity) {
		throw new Error(
			`${head}'s rule has ${pat_args.length} arguments, expected ${expected_arity}`,
		);
	}

	const { locals: rec_locals } = open_pi(rec.ty, prefix_len);
	const env = new Map<string, Term>();
	const locals_in_order: Term[] = [];
	for (let i = 0; i < prefix_len; i++) {
		const a = pat_args[i]!;
		if (a.type !== "ident") throw new Error(`a pattern argument must be a variable`);
		if (env.has(a.ident)) {
			throw new Error(`the pattern variable '${a.ident}' is already bound`);
		}
		env.set(a.ident, rec_locals[i]!);
		locals_in_order.push(rec_locals[i]!);
	}
	const param_locals = locals_in_order.slice(0, info.num_params);
	const motive_local = locals_in_order[info.num_params]!;
	const index_pat_args = pat_args.slice(prefix_len, prefix_len + info.num_indices);

	const last = pat_args[pat_args.length - 1]!;
	const { head: ctor_name, args: ctor_pat_args } = spine(last);
	const ctor_global = globals.get(ctor_name);
	if (!ctor_global || ctor_global.ctor_of !== ind_name) {
		throw new Error(
			`expected type ${ctor_global?.ctor_of ?? ctor_name} to be a subtype of ${ind_name}`,
		);
	}

	const count = (info.rule_counts.get(ctor_name) ?? 0) + 1;
	info.rule_counts.set(ctor_name, count);
	if (count > 1) {
		throw new Error(`${count} rules match ${ctor_name}`);
	}

	const { locals: ctor_all_locals, body: ctor_concl } = open_pi(
		ctor_global.ty,
		Infinity,
		param_locals,
	);
	if (ctor_pat_args.length !== ctor_all_locals.length) {
		throw new Error(`${ctor_name}'s pattern has the wrong number of arguments`);
	}
	for (let i = 0; i < info.num_params; i++) {
		const a = ctor_pat_args[i]!;
		if (a.type !== "ident" || env.get(a.ident) !== param_locals[i]) {
			throw new Error(
				`expected type ${ind_name} to be applied to its own parameters`,
			);
		}
	}
	const field_locals: Term[] = [];
	for (let i = info.num_params; i < ctor_all_locals.length; i++) {
		const a = ctor_pat_args[i]!;
		if (a.type !== "ident") throw new Error(`a pattern field must be a variable`);
		if (env.has(a.ident)) {
			throw new Error(`the pattern variable '${a.ident}' is already bound`);
		}
		const l = ctor_all_locals[i]!;
		env.set(a.ident, l);
		field_locals.push(l);
	}
	locals_in_order.push(...field_locals);

	// The indices this rule fires at are whatever the constructor's own
	// conclusion forces them to be, not chosen by the rule - the only way to
	// name one here is to reuse an already-bound pattern variable that
	// happens to equal it (as `Eq`'s `a` does). Anything else would need
	// genuine multi-position matching, which isn't supported.
	const { args: ctor_concl_args } = unwind(ctor_concl);
	const forced_indices = ctor_concl_args.slice(info.num_params);
	for (let i = 0; i < info.num_indices; i++) {
		const a = index_pat_args[i]!;
		const bound = a.type === "ident" ? env.get(a.ident) : undefined;
		if (bound === undefined || !defeq(globals, bound, forced_indices[i]!)) {
			throw new Error(
				`@iota(${ind_name}) cannot match on ${1 + info.num_indices} arguments at once`,
			);
		}
	}

	const target_term = apply({ k: "global", name: ctor_name }, [
		...param_locals,
		...field_locals,
	]);
	const expected_ty = apply(motive_local, [...forced_indices, target_term]);

	const declared_ty = elab_expr(globals, stmt.ty, env);
	if (!defeq(globals, declared_ty, expected_ty)) {
		throw new Error(`the rule claims ${print(declared_ty)}`);
	}

	if (stmt.def === null) throw new Error(`the pattern rule has no body`);
	const rhs = elab_expr(globals, stmt.def, env);
	check(globals, rhs, expected_ty);
	check_structural(globals, head, rec_arity(info), field_locals, rhs);

	info.rules.set(ctor_name, { locals: locals_in_order, rhs });
}
