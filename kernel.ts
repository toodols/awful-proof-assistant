// The kernel: dependent function types over sorts, beta and delta reduction,
import { spine } from "./inductive";
import type { Expr } from "./parser";

// definitional equality, and type inference. It is all a logic needs; the
// native values and the inductive machinery plug in from outside.

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
	| { k: "nat"; n: bigint }
	// a native string value of whichever type @lang(String) named
	| { k: "str"; s: string };

export type Local = Term & { k: "local" };

export let next_local_id = 0;

export function fresh_local(ty: Term): Local {
	return { k: "local", id: next_local_id++, ty };
}

export function instantiate(body: Term, value: Term, depth = 0): Term {
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

export function abstract_local(term: Term, l: Local, depth = 0): Term {
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

export function subst_locals(term: Term, map: Map<number, Term>): Term {
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

export function apply(fn: Term, args: Term[]): Term {
	return args.reduce((f, a) => ({ k: "app", fn: f, arg: a }) as Term, fn);
}

export function unwind(term: Term): { head: Term; args: Term[] } {
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
export function open_pi(
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
export function close_pi(locals: Term[], body: Term): Term {
	let out = body;
	for (let i = locals.length - 1; i >= 0; i--) {
		const l = locals[i] as Local;
		out = { k: "pi", dom: l.ty, body: abstract_local(out, l) };
	}
	return out;
}

export function final_sort(t: Term): Sort {
	let cur = t;
	while (cur.k === "pi") cur = cur.body;
	if (cur.k !== "sort") throw new Error(`expected a type ending in a sort`);
	return cur.s;
}

export function print(t: Term): string {
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
		case "str":
			return JSON.stringify(t.s);
	}
}

// ---------------------------------------------------------------------------
// Globals
// ---------------------------------------------------------------------------

export type IotaRule = { locals: Term[]; rhs: Term };

export type RecInfo = {
	ind: string;
	num_params: number;
	num_indices: number;
	ctor_order: string[];
	rules: Map<string, IotaRule>;
	rule_counts: Map<string, number>;
};

export type Global = {
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
	// set on a constructor marked @lang(Nat.zero) or @lang(Nat.succ): which
	// native value whnf turns it into (or apart into), on the way to and from
	// a `nat` Term.
	lang_role?: string;
};

export type Globals = Map<string, Global>;

export function new_globals(): Globals {
	return new Map();
}

export function rec_arity(info: RecInfo): number {
	return info.num_params + 1 + info.ctor_order.length + info.num_indices + 1;
}

// ---------------------------------------------------------------------------
// Reduction and definitional equality
// ---------------------------------------------------------------------------

// Extension points for native values. The kernel knows `nat` and `str` as
// opaque literal terms and nothing else about them; whatever gives them
// meaning installs itself here.
export type Hooks = {
	reduce?: (globals: Globals, role: string, args: Term[]) => Term | null;
	spine?: (globals: Globals, ind: string, target: Term) => { head: Term; args: Term[] } | null;
	unfold?: (globals: Globals, t: Term) => Term | null;
	infer?: (globals: Globals, t: Term) => Term | null;
};
export const hooks: Hooks = {};

// Every reduction step that continues with a new term is a loop iteration
// rather than a recursive call, so a function that recurses in tail position
// (as a comparison does) runs in constant stack however many steps it takes.
export function whnf(globals: Globals, term: Term): Term {
	for (;;) {
		const { head, args } = unwind(term);

		if (head.k === "global") {
			const g = globals.get(head.name);
			if (g?.lang_role !== undefined && hooks.reduce) {
				const next = hooks.reduce(globals, g.lang_role, args);
				if (next !== null) {
					term = next;
					continue;
				}
			}
			if (g?.def) {
				term = apply(g.def, args);
				continue;
			}
			if (g?.rec_info) {
				const info = g.rec_info;
				const arity = rec_arity(info);
				if (args.length >= arity) {
					const target = whnf(globals, args[arity - 1]!);
					const spine = hooks.spine?.(globals, info.ind, target) ?? unwind(target);
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
							term = apply(reduced, args.slice(arity));
							continue;
						}
					}
				}
			}
		}

		if (head.k === "lam" && args.length > 0) {
			const [first, ...rest] = args as [Term, ...Term[]];
			term = apply(instantiate(head.body, first), rest);
			continue;
		}

		return apply(head, args);
	}
}

// Whether two terms are literally the same tree, without reducing anything.
// Checked before defeq starts reducing: two copies of one stuck term (as a
// proof statement and the type it is checked against often are) would
// otherwise be compared by unfolding both side by side, which for a
// comparison against a big literal means unfolding it layer by layer.
export function same_term(a: Term, b: Term): boolean {
	if (a === b) return true;
	if (a.k !== b.k) return false;
	switch (a.k) {
		case "sort":
			return a.s === (b as typeof a).s;
		case "bvar":
			return a.i === (b as typeof a).i;
		case "local":
			return a.id === (b as typeof a).id;
		case "global":
			return a.name === (b as typeof a).name;
		case "nat":
			return a.n === (b as typeof a).n;
		case "str":
			return a.s === (b as typeof a).s;
		case "app":
			return (
				same_term(a.fn, (b as typeof a).fn) && same_term(a.arg, (b as typeof a).arg)
			);
		case "lam":
		case "pi":
			return (
				same_term(a.dom, (b as typeof a).dom) &&
				same_term(a.body, (b as typeof a).body)
			);
	}
}

export function defeq(globals: Globals, a: Term, b: Term): boolean {
	if (same_term(a, b)) return true;
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

export function structural_defeq(globals: Globals, wa: Term, wb: Term): boolean {
	if (wa === wb) return true;
	if (wa.k === "sort" && wb.k === "sort") return wa.s === wb.s;
	if (wa.k === "local" && wb.k === "local") return wa.id === wb.id;
	if (wa.k === "global" && wb.k === "global") return wa.name === wb.name;
	if (wa.k === "bvar" && wb.k === "bvar") return wa.i === wb.i;
	if (wa.k === "nat" && wb.k === "nat") return wa.n === wb.n;
	if (wa.k === "str" && wb.k === "str") return wa.s === wb.s;
	if (wb.k === "app" && hooks.unfold) {
		const u = hooks.unfold(globals, wa);
		if (u !== null) return defeq(globals, u, wb);
	}
	if (wa.k === "app" && hooks.unfold) {
		const u = hooks.unfold(globals, wb);
		if (u !== null) return defeq(globals, wa, u);
	}
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
export const prop_typed_cache = new Map<number, boolean>();

export function is_prop_typed(globals: Globals, t: Term): boolean {
	if (t.k === "local") {
		const cached = prop_typed_cache.get(t.id);
		if (cached !== undefined) return cached;
		const result = compute_is_prop_typed(globals, t);
		prop_typed_cache.set(t.id, result);
		return result;
	}
	return compute_is_prop_typed(globals, t);
}

export function compute_is_prop_typed(globals: Globals, t: Term): boolean {
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

export function as_sort(globals: Globals, t: Term): Sort {
	const w = whnf(globals, t);
	if (w.k !== "sort") throw new Error(`expected a type, found ${print(w)}`);
	return w.s;
}

export function check_is_type(globals: Globals, term: Term): void {
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
		case "nat":
		case "str": {
			const ty = hooks.infer?.(globals, term) ?? null;
			if (ty === null) throw new Error(`a literal needs a native type in scope`);
			return ty;
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
