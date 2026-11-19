// A dependently-typed checker: universes Prop/Type/Type1, pi/lambda, beta
// reduction, and inductive types (@inductive/@intro(X)/@rec(X)) whose
// recursor is derived from the constructors and compared against what was
// declared, plus pattern-match declarations (@iota(X)) whose rules are
// checked as the recursor's reduction rules and used to reduce it.
import type { Directive, Expr, Statement } from "./parser";

// ---------------------------------------------------------------------------
// Core terms
//
// Bound variables are de Bruijn indices while a binder body is still closed;
// while checking under a binder, the body is opened by substituting a fresh
// opaque `local` (carrying its own type) for bound-variable 0, so inference
// never needs a separate typing context - a local's type is right there on
// the node.
// ---------------------------------------------------------------------------

export type Sort = 0 | 1 | 2; // Prop, Type, Type1

export type Term =
	| { k: "sort"; s: Sort }
	| { k: "bvar"; i: number }
	| { k: "local"; id: number; ty: Term }
	| { k: "global"; name: string }
	| { k: "app"; fn: Term; arg: Term }
	| { k: "lam"; dom: Term; body: Term }
	| { k: "pi"; dom: Term; body: Term }
	// a native bigint value of whichever type @lang(Nat) named
	| { k: "nat"; n: bigint };

type Local = Term & { k: "local" };

let next_local_id = 0;
function fresh_local(ty: Term): Local {
	return { k: "local", id: next_local_id++, ty };
}

function instantiate(body: Term, value: Term, depth = 0): Term {
	switch (body.k) {
		case "bvar":
			return body.i === depth ? value : body;
		case "app":
			return {
				k: "app",
				fn: instantiate(body.fn, value, depth),
				arg: instantiate(body.arg, value, depth),
			};
		case "lam":
			return {
				k: "lam",
				dom: instantiate(body.dom, value, depth),
				body: instantiate(body.body, value, depth + 1),
			};
		case "pi":
			return {
				k: "pi",
				dom: instantiate(body.dom, value, depth),
				body: instantiate(body.body, value, depth + 1),
			};
		default:
			return body;
	}
}

function abstract_local(term: Term, l: Local, depth = 0): Term {
	switch (term.k) {
		case "local":
			return term.id === l.id ? { k: "bvar", i: depth } : term;
		case "app":
			return {
				k: "app",
				fn: abstract_local(term.fn, l, depth),
				arg: abstract_local(term.arg, l, depth),
			};
		case "lam":
			return {
				k: "lam",
				dom: abstract_local(term.dom, l, depth),
				body: abstract_local(term.body, l, depth + 1),
			};
		case "pi":
			return {
				k: "pi",
				dom: abstract_local(term.dom, l, depth),
				body: abstract_local(term.body, l, depth + 1),
			};
		default:
			return term;
	}
}

function subst_locals(term: Term, map: Map<number, Term>): Term {
	switch (term.k) {
		case "local":
			return map.get(term.id) ?? term;
		case "app":
			return {
				k: "app",
				fn: subst_locals(term.fn, map),
				arg: subst_locals(term.arg, map),
			};
		case "lam":
			return {
				k: "lam",
				dom: subst_locals(term.dom, map),
				body: subst_locals(term.body, map),
			};
		case "pi":
			return {
				k: "pi",
				dom: subst_locals(term.dom, map),
				body: subst_locals(term.body, map),
			};
		default:
			return term;
	}
}

function apply(fn: Term, args: Term[]): Term {
	return args.reduce((f, a) => ({ k: "app", fn: f, arg: a }) as Term, fn);
}

function unwind(term: Term): { head: Term; args: Term[] } {
	const args: Term[] = [];
	let cur = term;
	while (cur.k === "app") {
		args.push(cur.arg);
		cur = cur.fn;
	}
	args.reverse();
	return { head: cur, args };
}

// Opens up to `n` leading pi binders (n = Infinity for "all of them"),
// reusing `forced` for the outermost ones and fresh locals after that.
function open_pi(
	term: Term,
	n: number,
	forced: Term[] = [],
): { locals: Term[]; body: Term } {
	const locals: Term[] = [];
	let cur = term;
	while (cur.k === "pi" && locals.length < n) {
		const v = forced[locals.length] ?? fresh_local(cur.dom);
		locals.push(v);
		cur = instantiate(cur.body, v);
	}
	return { locals, body: cur };
}

// Wraps `body` in nested pi's over `locals`, right to left, so an earlier
// local's domain may itself mention a later one only if it was already
// abstracted - i.e. locals must be given in dependency order.
function close_pi(locals: Term[], body: Term): Term {
	let out = body;
	for (let i = locals.length - 1; i >= 0; i--) {
		const l = locals[i] as Local;
		out = { k: "pi", dom: l.ty, body: abstract_local(out, l) };
	}
	return out;
}

function final_sort(t: Term): Sort {
	let cur = t;
	while (cur.k === "pi") cur = cur.body;
	if (cur.k !== "sort") throw new Error(`expected a type ending in a sort`);
	return cur.s;
}

function print(t: Term): string {
	switch (t.k) {
		case "sort":
			return t.s === 0 ? "Prop" : t.s === 1 ? "Type" : "Type1";
		case "global":
			return t.name;
		case "local":
			return `?${t.id}`;
		case "bvar":
			return `#${t.i}`;
		case "app":
			return `(${print(t.fn)} ${print(t.arg)})`;
		case "lam":
			return `(fun (_ : ${print(t.dom)}) => ...)`;
		case "pi":
			return `(${print(t.dom)} -> ...)`;
		case "nat":
			return String(t.n);
	}
}

// ---------------------------------------------------------------------------
// Globals
// ---------------------------------------------------------------------------

type IotaRule = { locals: Term[]; rhs: Term };

type RecInfo = {
	ind: string;
	num_params: number;
	num_indices: number;
	ctor_order: string[];
	rules: Map<string, IotaRule>;
	rule_counts: Map<string, number>;
};

type Global = {
	ty: Term;
	def: Term | null;
	is_inductive?: boolean;
	ctors?: string[];
	// memoized once the first @rec for this inductive computes it: the
	// constructors are fixed by then, so a second @rec on the same type (as
	// Lift.rec and Lift.rec_prop both are) does not need to re-derive it.
	num_params?: number;
	ctor_of?: string;
	rec_info?: RecInfo;
	// set on a constructor once it is confirmed to have the shape @lang(Nat)
	// needs: which native value whnf turns it into (or apart into), on the
	// way to and from a `nat` Term.
	lang_role?: "zero" | "succ";
};

export type Globals = Map<string, Global>;

// Which inductive, if any, @lang(Nat) named in this program - kept out of
// the Globals map itself (a plain `Map<string, Global>`, which every caller
// already constructs and passes around) so the exported type does not have
// to grow a field nothing else needs to know about.
type LangInfo = { nat?: string };
const lang_registry = new WeakMap<Globals, LangInfo>();
function lang_info(globals: Globals): LangInfo {
	let info = lang_registry.get(globals);
	if (!info) {
		info = {};
		lang_registry.set(globals, info);
	}
	return info;
}

export function new_globals(): Globals {
	return new Map();
}

function rec_arity(info: RecInfo): number {
	return info.num_params + 1 + info.ctor_order.length + info.num_indices + 1;
}

// ---------------------------------------------------------------------------
// Reduction and definitional equality
// ---------------------------------------------------------------------------

// A `nat`/`str` value, spelled out as the constructor application it stands
// for - one layer only (its own fields stay `nat`/`str` too), so recursor
// matching can treat a native value exactly like an ordinary constructor
// application without knowing natives exist.
function native_ctor_spine(
	globals: Globals,
	ind_name: string,
	target: Term,
): { head: Term; args: Term[] } | null {
	if (target.k !== "nat") return null;
	const ctors = globals.get(ind_name)?.ctors;
	const zero = ctors?.[0];
	const succ = ctors?.[1];
	if (!zero || !succ) return null;
	if (target.n <= 0n) return { head: { k: "global", name: zero }, args: [] };
	return {
		head: { k: "global", name: succ },
		args: [{ k: "nat", n: target.n - 1n }],
	};
}

function whnf(globals: Globals, term: Term): Term {
	const { head, args } = unwind(term);

	if (head.k === "global") {
		const g = globals.get(head.name);
		if (g?.lang_role === "zero") {
			return apply({ k: "nat", n: 0n }, args);
		}
		if (g?.lang_role === "succ" && args.length >= 1) {
			const n = whnf(globals, args[0]!);
			if (n.k === "nat") {
				return whnf(globals, apply({ k: "nat", n: n.n + 1n }, args.slice(1)));
			}
		}
		if (g?.def) {
			return whnf(globals, apply(g.def, args));
		}
		if (g?.rec_info) {
			const info = g.rec_info;
			const arity = rec_arity(info);
			if (args.length >= arity) {
				const target = whnf(globals, args[arity - 1]!);
				const spine = native_ctor_spine(globals, info.ind, target) ?? unwind(target);
				const { head: th, args: cargs } = spine;
				if (th.k === "global") {
					const rule = info.rules.get(th.name);
					if (rule) {
						const prefix_len = info.num_params + 1 + info.ctor_order.length;
						const prefix = args.slice(0, prefix_len);
						const fields = cargs.slice(info.num_params);
						const provided = [...prefix, ...fields];
						const map = new Map<number, Term>();
						rule.locals.forEach((l, i) => {
							map.set((l as Local).id, provided[i]!);
						});
						const reduced = subst_locals(rule.rhs, map);
						return whnf(globals, apply(reduced, args.slice(arity)));
					}
				}
			}
		}
	}

	if (head.k === "lam" && args.length > 0) {
		const [first, ...rest] = args as [Term, ...Term[]];
		return whnf(globals, apply(instantiate(head.body, first), rest));
	}

	return apply(head, args);
}

function defeq(globals: Globals, a: Term, b: Term): boolean {
	const wa = whnf(globals, a);
	const wb = whnf(globals, b);
	if (structural_defeq(globals, wa, wb)) return true;
	// Proof irrelevance: any two well-typed inhabitants of the same Prop are
	// interchangeable, since a Prop never lets a proof reveal which one it is.
	// This is checked last, and on the whnf'd terms directly, so it also
	// catches two structurally different but still Prop-typed subterms deep
	// inside an otherwise-matching application or binder.
	return is_prop_typed(globals, wa) && is_prop_typed(globals, wb);
}

function structural_defeq(globals: Globals, wa: Term, wb: Term): boolean {
	if (wa === wb) return true;
	if (wa.k === "sort" && wb.k === "sort") return wa.s === wb.s;
	if (wa.k === "local" && wb.k === "local") return wa.id === wb.id;
	if (wa.k === "global" && wb.k === "global") return wa.name === wb.name;
	if (wa.k === "bvar" && wb.k === "bvar") return wa.i === wb.i;
	if (wa.k === "nat" && wb.k === "nat") return wa.n === wb.n;
	if (wa.k === "app" && wb.k === "app") {
		return defeq(globals, wa.fn, wb.fn) && defeq(globals, wa.arg, wb.arg);
	}
	if (wa.k === "pi" && wb.k === "pi") {
		if (!defeq(globals, wa.dom, wb.dom)) return false;
		const l = fresh_local(wa.dom);
		return defeq(globals, instantiate(wa.body, l), instantiate(wb.body, l));
	}
	if (wa.k === "lam" && wb.k === "lam") {
		if (!defeq(globals, wa.dom, wb.dom)) return false;
		const l = fresh_local(wa.dom);
		return defeq(globals, instantiate(wa.body, l), instantiate(wb.body, l));
	}
	return false;
}

// Whether `t`'s own type is a Prop, i.e. whether `t` is a proof. Locals are
// immutable once created and commonly re-checked against each other many
// times within one proof (the same hypothesis used at several call sites),
// so their answer is cached by id rather than re-inferred every time.
const prop_typed_cache = new Map<number, boolean>();

function is_prop_typed(globals: Globals, t: Term): boolean {
	if (t.k === "local") {
		const cached = prop_typed_cache.get(t.id);
		if (cached !== undefined) return cached;
		const result = compute_is_prop_typed(globals, t);
		prop_typed_cache.set(t.id, result);
		return result;
	}
	return compute_is_prop_typed(globals, t);
}

function compute_is_prop_typed(globals: Globals, t: Term): boolean {
	try {
		const ty = infer(globals, t);
		return as_sort(globals, infer(globals, ty)) === 0;
	} catch {
		return false;
	}
}

// ---------------------------------------------------------------------------
// Inference and checking
// ---------------------------------------------------------------------------

function as_sort(globals: Globals, t: Term): Sort {
	const w = whnf(globals, t);
	if (w.k !== "sort") throw new Error(`expected a type, found ${print(w)}`);
	return w.s;
}

function check_is_type(globals: Globals, term: Term): void {
	// Type1 is the top of the ladder and has no type of its own, but it is
	// still a perfectly good classifier for other terms - only a term that
	// isn't already a sort needs its own inferred type to land in one.
	const w = whnf(globals, term);
	if (w.k === "sort") return;
	as_sort(globals, infer(globals, term));
}

export function infer(globals: Globals, term: Term): Term {
	switch (term.k) {
		case "sort":
			if (term.s === 2) throw new Error(`Type1 has no type`);
			return { k: "sort", s: (term.s + 1) as Sort };
		case "local":
			return term.ty;
		case "global": {
			const g = globals.get(term.name);
			if (!g) throw new Error(`${term.name} not defined`);
			return g.ty;
		}
		case "bvar":
			throw new Error(`internal error: unbound variable`);
		case "nat": {
			const name = lang_info(globals).nat;
			if (!name) throw new Error(`a numeral needs an @lang(Nat) type in scope`);
			return { k: "global", name };
		}
		case "app": {
			const tf = whnf(globals, infer(globals, term.fn));
			if (tf.k !== "pi") {
				throw new Error(`applying ${print(tf)}, which is not a function`);
			}
			check(globals, term.arg, tf.dom);
			return instantiate(tf.body, term.arg);
		}
		case "lam": {
			check_is_type(globals, term.dom);
			const l = fresh_local(term.dom);
			const body_ty = infer(globals, instantiate(term.body, l));
			return { k: "pi", dom: term.dom, body: abstract_local(body_ty, l) };
		}
		case "pi": {
			const sa = as_sort(globals, infer(globals, term.dom));
			const l = fresh_local(term.dom);
			const sb = as_sort(globals, infer(globals, instantiate(term.body, l)));
			return { k: "sort", s: (sb === 0 ? 0 : Math.max(sa, sb)) as Sort };
		}
	}
}

export function check(globals: Globals, term: Term, expected: Term): void {
	const actual = infer(globals, term);
	if (!defeq(globals, actual, expected)) {
		throw new Error(
			`type mismatch: expected ${print(expected)}, found ${print(actual)}`,
		);
	}
}

// ---------------------------------------------------------------------------
// Elaboration: surface Expr -> Term
// ---------------------------------------------------------------------------

function elab_expr(globals: Globals, expr: Expr, env: Map<string, Term>): Term {
	if (expr.type === "ident") {
		const local = env.get(expr.ident);
		if (local) return local;
		if (expr.ident === "Prop") return { k: "sort", s: 0 };
		if (expr.ident === "Type") return { k: "sort", s: 1 };
		if (expr.ident === "Type1") return { k: "sort", s: 2 };
		if (!globals.has(expr.ident)) {
			throw new Error(`${expr.ident} not defined`);
		}
		return { k: "global", name: expr.ident };
	}
	if (expr.type === "nat_lit") return { k: "nat", n: expr.value };
	if (expr.type === "application") {
		return {
			k: "app",
			fn: elab_expr(globals, expr.fun, env),
			arg: elab_expr(globals, expr.value, env),
		};
	}
	if (expr.type === "lambda" || expr.type === "pi") {
		const binding = expr.head.type === "binding" ? expr.head : null;
		const dom = elab_expr(globals, binding ? binding.ty : expr.head, env);
		const l = fresh_local(dom);
		// Mutate `env` in place rather than copying it for every binder (which
		// would make a chain of n nested binders cost O(n^2)), restoring
		// whatever `binding.ident` shadowed once this binder's body is done.
		// Safe because elaboration is single-threaded recursive descent and a
		// thrown error abandons `env` entirely rather than resuming with it.
		let body: Term;
		if (binding) {
			const had = env.has(binding.ident);
			const prev = env.get(binding.ident);
			env.set(binding.ident, l);
			body = elab_expr(globals, expr.tail, env);
			if (had) env.set(binding.ident, prev!);
			else env.delete(binding.ident);
		} else {
			body = elab_expr(globals, expr.tail, env);
		}
		return {
			k: expr.type === "lambda" ? "lam" : "pi",
			dom,
			body: abstract_local(body, l),
		};
	}
	// expr.type === "binding"
	throw new Error(`found a binding outside lambda or pi`);
}

// ---------------------------------------------------------------------------
// Inductive types: parameter counting and recursor derivation
// ---------------------------------------------------------------------------

// The largest prefix of the inductive's own binders that every constructor's
// conclusion applies unchanged, in the same position. For a simple type this
// is exactly the intuitive parameter list; for `Eq A a b` this mechanically
// also picks up `a`, which is exactly what makes the derived recursor the
// usual based (J-style) eliminator rather than one that quantifies `a` too.
function count_core_params(ind_ty: Term, ctor_tys: Term[]): number {
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

function derive_recursor_type(
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

function derive_and_validate_recursor(
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

export type CheckOptions = {
	require_markers?: boolean;
	on_checked?: (stmt: Statement, ms: number) => void;
};

function spine(expr: Expr): { head: string; args: Expr[] } {
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

const MARKERS = ["axiom", "inductive", "intro", "rec"];

// @lang(Nat) needs the constructors it names, in @intro order: a
// zero-argument one first, then a second whose only field is - directly,
// not behind a further binder - the type itself. That is exactly a Peano
// numeral's shape, which native `nat` values stand in for one layer at a
// time.
function validate_nat_ctor(
	ind_name: string,
	name: string,
	ty: Term,
	position: number,
): "zero" | "succ" {
	if (position === 1) {
		const { locals } = open_pi(ty, Infinity);
		if (locals.length !== 0) {
			throw new Error(
				`@lang(Nat): ${name} has to be the zero constructor, taking no arguments`,
			);
		}
		return "zero";
	}
	if (position === 2) {
		const { locals } = open_pi(ty, Infinity);
		if (locals.length !== 1) {
			throw new Error(`@lang(Nat): ${name} has to take exactly one ${ind_name} field`);
		}
		const field = locals[0] as Local;
		const head = unwind(field.ty).head;
		if (!(head.k === "global" && head.name === ind_name)) {
			throw new Error(`@lang(Nat): ${name}'s field has to be ${ind_name} itself`);
		}
		return "succ";
	}
	throw new Error(`@lang(Nat): ${ind_name} may only have two constructors (zero and succ)`);
}

function occurs_in(name: string, t: Term): boolean {
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
function check_strictly_positive(ind_name: string, arg: Term): void {
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
function check_ctor_positivity(ind_name: string, ty: Term): void {
	let cur = ty;
	while (cur.k === "pi") {
		check_strictly_positive(ind_name, cur.dom);
		cur = cur.body;
	}
}

function check_decl(
	globals: Globals,
	stmt: Statement,
	opts: CheckOptions,
): void {
	const name = (stmt.pat as Expr & { type: "ident" }).ident;
	if (globals.has(name)) throw new Error(`${name} already defined`);

	// @lang is an extra annotation rather than an alternative marker: it only
	// ever rides along with @inductive, so it is counted separately from the
	// "exactly one marker" rule below.
	const lang_directive = stmt.directives.find((d) => d.name === "lang") ?? null;
	const directives = stmt.directives.filter((d) => d.name !== "lang");
	const require_markers = opts.require_markers ?? true;

	if (directives.length > 1) {
		throw new Error(
			`${name} has ${directives.length} markers, but a declaration gets exactly one marker`,
		);
	}
	const marker: Directive | null = directives[0] ?? null;
	if (marker === null) {
		// only a bodiless declaration is an assumption that needs a marker to
		// say so; one with a definition is proved, not trusted.
		if (require_markers && stmt.def === null) {
			throw new Error(
				`${name} must be marked @axiom, @inductive, @intro(...) or @rec(...)`,
			);
		}
	} else {
		if (marker.name === "iota") {
			throw new Error(`@iota marks a rule, not a declaration`);
		}
		if (!MARKERS.includes(marker.name)) {
			throw new Error(`@${marker.name} is not a valid marker`);
		}
		if (stmt.def !== null) {
			throw new Error(
				`${name} is marked @${marker.name} and so may not have a definition`,
			);
		}
	}
	if (lang_directive !== null && marker?.name !== "inductive") {
		throw new Error(`@lang(${lang_directive.arg}) may only mark an @inductive declaration`);
	}
	if (lang_directive !== null && lang_directive.arg !== "Nat") {
		throw new Error(`@lang only supports Nat, not ${lang_directive.arg}`);
	}

	const env = new Map<string, Term>();
	const ty_term = elab_expr(globals, stmt.ty, env);
	check_is_type(globals, ty_term);

	let def_term: Term | null = null;
	if (stmt.def !== null) {
		def_term = elab_expr(globals, stmt.def, env);
		check(globals, def_term, ty_term);
	}

	const g: Global = { ty: ty_term, def: def_term };
	globals.set(name, g);

	if (marker?.name === "inductive") {
		g.is_inductive = true;
		g.ctors = [];
		if (lang_directive !== null) {
			const info = lang_info(globals);
			if (info.nat !== undefined) {
				throw new Error(`@lang(Nat) is already ${info.nat}`);
			}
			info.nat = name;
		}
	} else if (marker?.name === "intro") {
		const ind_name = marker.arg;
		if (ind_name === null) {
			throw new Error(`@intro needs the inductive type it introduces`);
		}
		const ind = globals.get(ind_name);
		if (!ind || !ind.is_inductive) {
			throw new Error(`${ind_name} is not a declared inductive type`);
		}
		const { body } = open_pi(ty_term, Infinity);
		const { head } = unwind(body);
		if (!(head.k === "global" && head.name === ind_name)) {
			throw new Error(`${name} does not conclude in ${ind_name}`);
		}
		check_ctor_positivity(ind_name, ty_term);
		g.ctor_of = ind_name;
		ind.ctors!.push(name);
		if (lang_info(globals).nat === ind_name) {
			g.lang_role = validate_nat_ctor(ind_name, name, ty_term, ind.ctors!.length);
		}
	} else if (marker?.name === "rec") {
		const ind_name = marker.arg;
		if (ind_name === null) {
			throw new Error(`@rec needs the inductive type it recurses on`);
		}
		const ind = globals.get(ind_name);
		if (!ind || !ind.is_inductive) {
			throw new Error(`${ind_name} is not a declared inductive type`);
		}
		g.rec_info = derive_and_validate_recursor(globals, ind_name, ind, ty_term);
	}
}

function check_iota_rule(globals: Globals, stmt: Statement): void {
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

	info.rules.set(ctor_name, { locals: locals_in_order, rhs });
}

export function check_stmt(
	globals: Globals,
	stmt: Statement,
	opts: CheckOptions = {},
): void {
	if (stmt.pat.type === "ident") {
		check_decl(globals, stmt, opts);
	} else {
		check_iota_rule(globals, stmt);
	}
}

export function check_program(
	globals: Globals,
	stmts: Statement[],
	opts: CheckOptions = {},
): void {
	for (const stmt of stmts) {
		const started = performance.now();
		check_stmt(globals, stmt, opts);
		opts.on_checked?.(stmt, performance.now() - started);
	}
	for (const g of globals.values()) {
		if (
			g.rec_info &&
			g.rec_info.rules.size > 0 &&
			g.rec_info.rules.size !== g.rec_info.ctor_order.length
		) {
			throw new Error(`no rule for every constructor`);
		}
	}
}
