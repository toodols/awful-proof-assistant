import { file, write } from "bun"; // i stop being able to import txt when i remove this for some reason
import { first_ident, type Expr, type Statement, type Token } from "./parser";

type Globals = {
	[k: string]: {
		ty: Expr;
		def: Expr | null;
		// A rule: the pattern, the type the declaration gives at that pattern,
		// the body, which opaque value each pattern variable was given so that
		// matching can substitute into the body, and the inductive its @iota
		// named, if it was marked. Every rule reduces; the marked ones are the
		// ones the checker has something to say about.
		rules: {
			pat: Expr;
			ty: Expr;
			def: Expr;
			var_ids: (number | undefined)[];
			iota: string | null;
			// spine_args(pat), cached since reduce_iota looks this up on
			// every reduction step that reaches this rule's declaration
			pat_args: Expr[];
		}[];
		// whether the rules marked @iota cover the type they match on yet
		iota_complete?: boolean;
		// set by @inductive; constructors are filled in by @intro(...)
		inductive?: { constructors: string[]; num_params?: number };
		// set by @rec(X): which type this eliminates. Reduction never reads it
		// - it is only how @iota(X) knows whose rules these are meant to be.
		rec?: string;
	};
};
const error_ty = { type: "error" as const, tokens: [] as Token[] };

// The universes, smallest first: `Prop` is 0, `Type` is 1, `Type1` is 2.
// `Type : Type1` and `Type1` is the top of the ladder, so nothing types it -
// which is what keeps `Type : Type` from being provable here.
const SORT_NAMES = ["Prop", "Type", "Type1"];

// The universe an expression names, or -1 if it does not name one.
function sort_index(expr: Expr): number {
	return expr.type === "global" ? SORT_NAMES.indexOf(expr.ident) : -1;
}

function sort_at(index: number): Expr {
	return {
		type: "global",
		ident: SORT_NAMES[index] ?? SORT_NAMES[SORT_NAMES.length - 1]!,
		tokens: [],
	};
}

// An opaque value of type `ty`, standing for a binder we cannot see inside of.
// Every call mints a fresh identity, so `(A : Type) -> (B : Type) -> A -> B`
// does not accept an `A` where it asked for a `B`.
let next_opaque_id = 0;
function opaque(ty: Expr): Expr {
	return { type: "value_with_type", id: next_opaque_id++, ty, tokens: [] };
}

export function new_globals() {
	const globals: Globals = {};

	// Type1 tops out the ladder and has no type of its own
	globals.Type1 = { ty: error_ty, def: null, rules: [] };
	globals.Type = {
		ty: {
			type: "global",
			ident: "Type1",
			tokens: [],
		},
		def: null,
		rules: [],
	};
	globals.Prop = {
		ty: {
			type: "global",
			ident: "Type",
			tokens: [],
		},
		def: null,
		rules: [],
	};
	globals.Any = {
		ty: {
			type: "any",
			tokens: [],
		},
		def: null,
		rules: [],
	};
	// For any type, SORRY `type` is a member of `type`
	// and SORRY <theorem> is a proof of <theorem>
	globals.SORRY = {
		ty: { type: "sorry", tokens: [] },
		def: null,
		rules: [],
	};
	return globals;
}

export function print_expr(expr: Expr): string {
	if (expr.type === "lambda") {
		return `(${print_expr(expr.head)} => ${print_expr(expr.tail)})`;
	} else if (expr.type === "pi") {
		return `(${print_expr(expr.head)} -> ${print_expr(expr.tail)})`;
	} else if (expr.type === "application") {
		return `(${print_expr(expr.fun)} ${print_expr(expr.value)})`;
	} else if (expr.type === "global") {
		return expr.ident;
	} else if (expr.type === "ref") {
		return `\\${expr.index}`;
	} else if (expr.type === "def") {
		return `@${expr.index}`;
	} else if (expr.type === "any") {
		return `Any`;
	} else if (expr.type === "value_with_type") {
		// the id tells two opaque values of the same type apart
		return `(_${expr.id} : ${print_expr(expr.ty)})`;
	} else {
		return `<${expr.type} is err>`;
	}
}

// The term a pattern spells out: its variables stand for the opaque values
// destructure gave them, and everything else is itself.
function pattern_term(
	pat: Expr,
	names: string[],
	destructured: Record<string, Expr>,
	bound: Expr,
): Expr {
	if (pat.type === "def") {
		return destructured[names[pat.index]!] ?? bound;
	} else if (pat.type === "global") {
		return pat;
	} else if (pat.type === "application") {
		return {
			type: "application",
			fun: pattern_term(pat.fun, names, destructured, bound),
			value: pattern_term(pat.value, names, destructured, bound),
			tokens: [],
		};
	}
	return bound;
}

// destructures a pattern against a type while storing name to their types
// \i = ref[i]
function destructure(
	globals: Globals,
	pat: Expr,
	ty: Expr,
	names: string[],
	destructured: Record<string, Expr>,
	// the opaque value this position was already given, if the caller made one
	value?: Expr,
): Expr {
	if (pat.type === "def") {
		const name = names[pat.index]!;
		const seen = destructured[name];
		if (seen !== undefined) {
			// The variable already stands for something, so this occurrence has
			// to stand for the same thing. That is what lets a clause name an
			// inductive's parameters twice, as
			// `Lst.rec A motive nil cons (Lst.cons A x xs)` has to.
			if (!member_of(globals, seen, ty)) {
				throw new Error(
					`the pattern variable '${name}' is used at two types: ${print_expr(
						type_of(globals, seen, {}, []),
					)} and ${print_expr(ty)}`,
				);
			}
			return ty;
		}
		destructured[name] = value ?? opaque(ty);
		return ty;
	} else if (pat.type === "application") {
		// pat.fun = ((A => B => C) b) c
		const fun_ty = destructure(
			globals,
			pat.fun,
			{ type: "any", tokens: [] },
			names,
			destructured,
		) as Expr & { type: "pi" };

		// fun_ty: B -> C;
		// tail = C;
		// head = B;
		const head = fun_ty.head;
		// the argument and every ref to it in the tail are the same value
		const bound = opaque(head);

		// b : B
		destructure(globals, pat.value, head, names, destructured, bound);

		// What the rest of the type gets to see here. A variable stands for an
		// arbitrary value of the domain, but a constructor pattern stands for
		// itself, so that a clause on `N.z` is given `motive N.z` and not
		// `motive <some N>`. Substituted the way an application is, so that the
		// argument actually reaches the binders that mention it.
		const arg = pattern_term(pat.value, names, destructured, bound);
		const tail = reduce_simp_app(
			globals,
			app_subst_new_refs(fun_ty.tail, arg),
		);
		if (!is_subtype(globals, tail, ty)) {
			throw new Error(
				`expected type ${print_expr(tail)} to be a subtype of ${print_expr(ty)}`,
			);
		}
		// DO NOT POP REFVALS
		return tail;
	} else if (pat.type === "global") {
		const var_ty = globals[pat.ident]!.ty;
		if (!is_subtype(globals, var_ty, ty)) {
			throw new Error(
				`expected type ${print_expr(var_ty)} to be a subtype of ${print_expr(ty)}`,
			);
		}
		return var_ty;
	} else if (pat.type === "lambda") {
		throw new Error("todo");
		// const pat_ty =  {
		// 	type: "pi",
		// 	head: pat.head,
		// 	tail: pat.tail,
		// 	tokens: [] as Token[],
		// } as const;
	} else if (pat.type === "pi") {
		const ty = { type: "global", ident: "Type", tokens: [] };
		throw new Error("todo");
	} else {
		throw new Error("wut");
	}
}

function type_of(
	globals: Globals,
	value: Expr,
	inner_defs: Record<string, Expr> = {},
	// \i : ref[i]
	ref_tys: Expr[] = [],
): Expr {
	// the type of identifier is its type in defs
	if (value.type === "global") {
		const def = globals[value.ident];
		if (!def) {
			throw new Error(`${value.ident} not defined`);
		}
		if (def.ty.type === "error") {
			throw new Error(
				`${value.ident} is the top universe, so it has no type`,
			);
		}
		return def.ty;
	} else if (value.type === "lambda") {
		// type of lambda is that but pi
		ref_tys.push(value.head);
		const res = {
			type: "pi",
			head: value.head,
			tail: type_of(globals, value.tail, inner_defs, ref_tys),
			tokens: [] as Token[],
		} as const;
		ref_tys.pop();
		return res;
	} else if (value.type === "pi") {
		// `(x : A) -> B` lives in Sort (imax u v): in Prop whenever B is,
		// however big A is - impredicativity - and otherwise in whichever of
		// the two universes is larger.
		ref_tys.push(value.head);
		let tail_ty: Expr;
		try {
			tail_ty = type_of(globals, value.tail, inner_defs, ref_tys);
		} finally {
			ref_tys.pop();
		}
		const v = sort_index(tail_ty);
		if (v === 0) return sort_at(0);
		// the domain is typed outside its own binder, so ref_tys is popped
		let u = -1;
		try {
			u = sort_index(type_of(globals, value.head, inner_defs, ref_tys));
		} catch {
			// a domain whose type we cannot work out cannot raise the
			// universe either; check_is_type is what rejects a bad one
		}
		return sort_at(Math.max(u, v, 1));
	} else if (value.type === "ref") {
		// only lambda can introduce expressions to ref in type_of so no conflicts with pi
		// however the ref could be referring to another ref
		// in that case we add the ref indices (this is actual black magic)
		const ref = ref_tys[ref_tys.length - value.index]!;
		if (ref) {
			// rename every subref in ref'd to itself + this ref's value.index
			return inc_refs_in_expr(ref, value.index);
		} else {
			return value;
		}
	} else if (value.type === "application") {
		// typeof(((a:Ty) => a) b) = apply(typeof(a), b)
		const fun_ty = type_of(globals, value.fun, inner_defs, ref_tys);
		if (fun_ty.type === "pi") {
			if (!member_of(globals, value.value, fun_ty.head, inner_defs, ref_tys)) {
				throw new Error(
					`Type mismatch: ${print_expr(value.value)} has type ${print_expr(
						type_of(globals, value.value, inner_defs, ref_tys),
					)}, which is not a member of ${print_expr(fun_ty.head)}`,
				);
			}
			// rewrite every ref in tail that references the head
			return reduce_simp_app(
				globals,
				app_subst_new_refs(fun_ty.tail, value.value),
			);
		} else if (fun_ty.type === "sorry") {
			return value.value;
		} else {
			throw new Error(
				`attempt to apply ${print_expr(fun_ty)} with ${print_expr(value.value)}`,
			);
		}
	} else if (value.type === "value_with_type") {
		return value.ty;
	} else {
		throw new Error(`type_of: ${value.type}`);
	}
}

// Recursively increment all free refs in an expression by an integer.
// Bound refs inside nested lambdas/pi are not shifted.
function inc_refs_in_expr(value: Expr, inc: number, depth = 0): Expr {
	if (value.type === "ref") {
		if (value.index > depth) {
			return {
				type: "ref",
				index: value.index + inc,
				tokens: [],
			};
		}
		return value;
	} else if (value.type === "application") {
		return {
			type: "application",
			fun: inc_refs_in_expr(value.fun, inc, depth),
			value: inc_refs_in_expr(value.value, inc, depth),
			tokens: [] as Token[],
		};
	} else if (value.type === "pi") {
		return {
			type: "pi",
			head: inc_refs_in_expr(value.head, inc, depth),
			tail: inc_refs_in_expr(value.tail, inc, depth + 1),
			tokens: [] as Token[],
		};
	} else if (value.type === "lambda") {
		return {
			type: "lambda",
			head: inc_refs_in_expr(value.head, inc, depth),
			tail: inc_refs_in_expr(value.tail, inc, depth + 1),
			tokens: [] as Token[],
		};
	} else {
		return value;
	}
}

// ref indices are updated according to rules below in the case a type is applied on a type
// if the ref's index equals the depth, the value should have its refs combine with the tail's index
// if the ref is less than the depth, it does not change
// if the ref is greater than the depth, it refers outside, and must lose one index
function app_subst_new_refs(tail: Expr, value: Expr, depth = 1): Expr {
	if (tail.type === "ref") {
		if (tail.index === depth) {
			return inc_refs_in_expr(value, tail.index - 1);
		} else if (tail.index > depth) {
			return {
				type: "ref",
				index: tail.index - 1,
				tokens: [] as Token[],
			};
		} else {
			return tail;
		}
	} else if (tail.type === "application") {
		return {
			type: "application",
			fun: app_subst_new_refs(tail.fun, value, depth),
			value: app_subst_new_refs(tail.value, value, depth),
			tokens: [] as Token[],
		};
	} else if (tail.type === "pi") {
		return {
			type: "pi",
			head: app_subst_new_refs(tail.head, value, depth),
			tail: app_subst_new_refs(tail.tail, value, depth + 1),
			tokens: [] as Token[],
		};
	} else if (tail.type === "lambda") {
		return {
			type: "lambda",
			head: app_subst_new_refs(tail.head, value, depth),
			tail: app_subst_new_refs(tail.tail, value, depth + 1),
			tokens: [] as Token[],
		};
	} else if (tail.type === "global") {
		return {
			type: "global",
			ident: tail.ident,
			tokens: [] as Token[],
		};
	} else if (tail.type === "value_with_type") {
		// an opaque value keeps its identity; only its type can mention refs
		return {
			type: "value_with_type",
			id: tail.id,
			ty: app_subst_new_refs(tail.ty, value, depth),
			tokens: [] as Token[],
		};
	} else {
		throw new Error(`replace: ${tail.type}`);
	}
}

// aka beta reduction. reduces expressions of the form `(A => B) a`
// `X.rec p.. motive minors.. i.. (X.c p.. a..)` reduces to the minor premise
// for `c`, applied to the constructor's fields and then to an induction
// hypothesis for each field that recurses. Every step eats one constructor, so
// this terminates.
// ---------------------------------------------------------------------------
// Iota
//
// A recursor's iota rules are what it does on each constructor, and reduction
// fires them. Matching is the primitive here, so a recursor is an ordinary
// declaration rather than something reduction knows about, and a rule is the
// only place a pattern may appear: every other definition is written in terms
// of a recursor.
//
// Three things keep a pile of rules from being an axiom in disguise, and all
// three are checked in check_iota_rules: the rules split one argument and cover
// its type exactly once each, every rule claims the type the recursor already
// gives at that pattern, and every recursive call descends to a field of the
// constructor it matched.
// ---------------------------------------------------------------------------

// Replaces pattern variables with the terms matched against them. `depth` is
// how many binders have been crossed, which is how far a substituted term's own
// free refs have to move to still point at the same binders.
function subst_opaques(expr: Expr, sub: Map<number, Expr>, depth = 0): Expr {
	if (expr.type === "value_with_type") {
		const value = sub.get(expr.id);
		if (value !== undefined) {
			return depth === 0 ? value : inc_refs_in_expr(value, depth);
		}
		return {
			type: "value_with_type",
			id: expr.id,
			ty: subst_opaques(expr.ty, sub, depth),
			tokens: [],
		};
	} else if (expr.type === "application") {
		return {
			type: "application",
			fun: subst_opaques(expr.fun, sub, depth),
			value: subst_opaques(expr.value, sub, depth),
			tokens: [],
		};
	} else if (expr.type === "lambda" || expr.type === "pi") {
		// the domain is outside the binder the tail is inside of
		return {
			type: expr.type,
			head: subst_opaques(expr.head, sub, depth),
			tail: subst_opaques(expr.tail, sub, depth + 1),
			tokens: [],
		};
	}
	return expr;
}

// Matches one pattern against one argument, growing `binds` from pattern
// variable to the term it stands for. A variable that occurs twice has to be
// handed the same term both times, which is what lets a clause name an
// inductive's parameters on both sides of its pattern, as
// `List.rec A motive nil cons (List.cons A x xs)` has to.
function match_pattern(
	globals: Globals,
	pat: Expr,
	term: Expr,
	binds: Map<number, Expr>,
): boolean {
	if (pat.type === "def") {
		const seen = binds.get(pat.index);
		if (seen !== undefined) return struct_eq(globals, seen, term);
		binds.set(pat.index, term);
		return true;
	} else if (pat.type === "global") {
		return term.type === "global" && term.ident === pat.ident;
	} else if (pat.type === "application") {
		if (term.type !== "application") return false;
		return (
			match_pattern(globals, pat.fun, term.fun, binds) &&
			match_pattern(globals, pat.value, term.value, binds)
		);
	}
	return struct_eq(globals, pat, term);
}

// The iota step: a declaration standing in front of a constructor becomes the
// body of the rule for that constructor. This is the only place reduction on a
// constructor comes from - the checker knows nothing about recursors here, so
// every rule fires whether or not a marker asked for it to be checked.
function reduce_iota(globals: Globals | null, expr: Expr): Expr | null {
	if (globals === null) return null;
	const head = head_of(expr);
	if (head.type !== "global") return null;
	const decl = globals[head.ident];
	if (decl === undefined || decl.rules.length === 0) return null;
	const args = spine_args(expr);
	for (const rule of decl.rules) {
		const pat_args = rule.pat_args;
		if (args.length < pat_args.length) continue;
		const binds = new Map<number, Expr>();
		let matched = true;
		for (let i = 0; i < pat_args.length; i++) {
			if (!match_pattern(globals, pat_args[i]!, args[i]!, binds)) {
				matched = false;
				break;
			}
		}
		if (!matched) continue;
		const sub = new Map<number, Expr>();
		for (const [index, value] of binds) {
			const id = rule.var_ids[index];
			if (id === undefined) {
				matched = false;
				break;
			}
			sub.set(id, value);
		}
		if (!matched) continue;
		let out = subst_opaques(rule.def, sub);
		// whatever the rule was applied to beyond its pattern still applies
		for (const a of args.slice(pat_args.length)) {
			out = { type: "application", fun: out, value: a, tokens: [] };
		}
		return reduce_simp_app(globals, out);
	}
	return null;
}

function reduce_simp_app(globals: Globals | null, expr: Expr): Expr {
	if (expr.type === "application") {
		// the function has to be reduced first: in `f a b`, reducing `f a` is
		// what turns the outer application into a redex at all, which is how a
		// global that unfolds to several nested lambdas gets applied to all of
		// its arguments
		const fun = reduce_simp_app(globals, expr.fun);
		const value = reduce_simp_app(globals, expr.value);
		if (fun.type === "lambda") {
			return reduce_simp_app(globals, app_subst_new_refs(fun.tail, value));
		} else {
			const applied: Expr = {
				type: "application",
				fun,
				value,
				tokens: [],
			};
			return reduce_iota(globals, applied) ?? applied;
		}
	} else if (expr.type === "lambda") {
		return {
			type: "lambda",
			head: reduce_simp_app(globals, expr.head),
			tail: reduce_simp_app(globals, expr.tail),
			tokens: [],
		};
	} else if (expr.type === "pi") {
		return {
			type: "pi",
			head: reduce_simp_app(globals, expr.head),
			tail: reduce_simp_app(globals, expr.tail),
			tokens: [],
		};
	} else {
		return expr;
	}
}

function is_subtype(
	globals: Globals,
	subty: Expr,
	ty: Expr,
	// \i : ref[i]
	ref_tys: Expr[] = [],
): boolean {
	if (ty.type === "any") return true;
	return struct_eq(globals, subty, ty, ref_tys);
}

function member_of(
	defs: Globals,
	expr: Expr,
	ty: Expr,
	inner_defs: Record<string, Expr> = {},
	ref_tys: Expr[] = [],
): boolean {
	return is_subtype(
		defs,
		type_of(defs, expr, inner_defs, ref_tys),
		ty,
		ref_tys,
	);
}

// Rename ident in and out of bound variables to use de Bruijn indices and stuff
function norm_names(
	globals: Globals,
	expr: Expr,
	inner_defs: Record<string, Expr> = {},
	def_names?: string[],
	bound: (string | null)[] = [],
): Expr {
	if (expr.type === "application") {
		return {
			type: "application",
			fun: norm_names(globals, expr.fun, inner_defs, def_names, bound),
			value: norm_names(
				globals,
				expr.value,
				inner_defs,
				def_names,
				bound,
			),
			tokens: [],
		};
	} else if (expr.type === "lambda" || expr.type === "pi") {
		let new_head;
		// if head is a binding, push the binding's ident into bound
		// the binding's ty needs to be rewritten before the binding's ident is pushed into bound
		// after renaming binding.ty, it becomes the new head of the lambda
		if (expr.head.type === "binding") {
			new_head = norm_names(
				globals,
				expr.head.ty,
				inner_defs,
				def_names,
				bound,
			);
			bound.push(expr.head.ident);

			// if head is just a type expression, push null into bound
			// null is basically the equivalent of _ : Type bindings. Where the _ technically introduces a new bound variable
		} else {
			new_head = norm_names(
				globals,
				expr.head,
				inner_defs,
				def_names,
				bound,
			);
			bound.push(null);
		}

		const ret = {
			type: expr.type,
			head: new_head,
			// as for the tail, it is rewritten after the binding's ident is pushed into bound
			tail: norm_names(globals, expr.tail, inner_defs, def_names, bound),
			tokens: [],
		};
		// after renaming the head and tail, pop the binding's ident from bound because it has exited 'scope'
		bound.pop();
		return ret;
	} else if (expr.type === "ident") {
		// look backwards from bound for the first match of expr.ident
		// if there are any duplicates, the last one 'shadows' all the previous ones
		// if there are no matches, check globals
		// if it exists in globals, leave it alone
		// if it doesn't exist in globals, throw an error
		for (let i = 1; i <= bound.length; i++) {
			if (bound[bound.length - i] === expr.ident) {
				return {
					type: "ref",
					index: i,
					tokens: [],
				};
			}
		}
		if (expr.ident in globals) {
			if (globals[expr.ident]!.def !== null) {
				return globals[expr.ident]!.def!;
			}
			return {
				type: "global",
				ident: expr.ident,
				tokens: [],
			};
		} else if (expr.ident in inner_defs) {
			return inner_defs[expr.ident]!;
		} else if (def_names) {
			return {
				type: "def",
				index: def_names.push(expr.ident) - 1,
				tokens: [] as Token[],
			};
		} else {
			throw new Error(`${first_ident(expr).ident} not defined`);
		}
	} else if (expr.type === "binding") {
		throw new Error("found a binding outside lambda or pi");
	} else if (expr.type === "error") {
		throw new Error("error");
	} else if (expr.type === "ref") {
		throw new Error("error");
	}
	throw new Error("unreachable");
}

// Whether two expressions are structurally equal.
// Pass globals to enable proof irrelevance (any two proofs of the same Prop are equal).
// Pass null to do a plain structural comparison without proof irrelevance (used internally
// to compare types while checking proof irrelevance, avoiding infinite recursion).
// `ref_tys` is what makes proof irrelevance reach a bound variable: without it
// a proof that is a binder cannot be typed, so two proofs of the same Prop are
// only ever recognised as equal when both are closed.
function struct_eq(
	globals: Globals | null,
	a: Expr,
	b: Expr,
	ref_tys: Expr[] = [],
): boolean {
	// The plain structural comparison is by far the common case (identical
	// subterms after substitution), and is cheap. Only pay for the
	// type_of-based proof irrelevance check below when shapes actually
	// disagree - it cannot change a "true" verdict the shape check already
	// gave, only rescue a "false" one.
	if (struct_eq_shape(globals, a, b, ref_tys)) return true;
	if (globals !== null) {
		try {
			// copies: type_of pushes and pops as it goes and may throw part
			// way through, and the catch below would leave ours corrupted
			const ty_a = type_of(globals, a, {}, [...ref_tys]);
			const ty_b = type_of(globals, b, {}, [...ref_tys]);
			// use plain structural comparison for the type check to avoid infinite recursion
			if (struct_eq(null, ty_a, ty_b)) {
				const ty_ty = type_of(globals, ty_a, {}, [...ref_tys]);
				if (ty_ty.type === "global" && ty_ty.ident === "Prop") {
					return true;
				}
			}
		} catch {}
	}
	return false;
}

function struct_eq_shape(
	globals: Globals | null,
	a: Expr,
	b: Expr,
	ref_tys: Expr[],
): boolean {
	if (a.type === "application") {
		return (
			b.type === "application" &&
			struct_eq(globals, a.fun, b.fun, ref_tys) &&
			struct_eq(globals, a.value, b.value, ref_tys)
		);
	} else if (a.type === "lambda" || a.type === "pi") {
		if (b.type !== a.type) return false;
		// inside the binder the context has grown by one
		if (!struct_eq(globals, a.head, b.head, ref_tys)) return false;
		ref_tys.push(a.head);
		try {
			return struct_eq(globals, a.tail, b.tail, ref_tys);
		} finally {
			ref_tys.pop();
		}
	} else if (a.type === "global") {
		return b.type === "global" && a.ident === b.ident;
	} else if (a.type === "ref") {
		return b.type === "ref" && a.index === b.index;
	} else if (a.type === "value_with_type") {
		// opaque values are equal only when they came from the same binder
		return b.type === "value_with_type" && a.id === b.id;
	} else {
		throw new Error(`unreachable: ${a.type}`);
	}
}

// A declaration's type has to be a type. Without this an axiom could be
// stated with a nonsense type, because nothing else ever looks at the type of a
// declaration that has no definition. `Type` and `Prop` are sorts themselves,
// so they pass on sight.
function check_is_type(
	globals: Globals,
	ty: Expr,
	inner_defs: Record<string, Expr>,
	// \i : ref[i]
	ref_tys: Expr[] = [],
) {
	if (ty.type === "pi") {
		// `(x : A) -> B` is a type only if both halves are. Reading the sort off
		// the codomain alone would never look at A, which is where a term that
		// is not a type at all tends to be written by mistake.
		check_is_type(globals, ty.head, inner_defs, ref_tys);
		ref_tys.push(ty.head);
		try {
			check_is_type(globals, ty.tail, inner_defs, ref_tys);
		} finally {
			ref_tys.pop();
		}
		return;
	}
	if (sort_index(ty) >= 0) return;
	if (ty.type === "any" || ty.type === "sorry") return;
	const sort = type_of(globals, ty, inner_defs, ref_tys);
	if (sort_index(sort) < 0) {
		throw new Error(
			`${print_expr(ty)} is not a type: it has type ${print_expr(sort)}`,
		);
	}
}

// What a declaration with no `:=` is allowed to claim to be. Only `@axiom`
// means "take my word for it"; the other three are claims the checker is meant
// to verify, and until it can, saying so would be a lie.
const IMPLEMENTED_DIRECTIVES = [
	"axiom",
	"inductive",
	"intro",
	"rec",
	"iota",
];
const PLANNED_DIRECTIVES: string[] = [];


// ---------------------------------------------------------------------------
// Recursors
//
// Checking that a written recursor is *the* recursor means deriving the
// canonical one and comparing. The derivation is done locally nameless: each
// binder is opened into a fresh global whose name cannot be written in the
// language, so the recursor is assembled without any de Bruijn arithmetic, and
// closing it puts the indices back.
// ---------------------------------------------------------------------------

let next_sentinel = 0;
function sentinel(): Expr {
	return { type: "global", ident: `#${next_sentinel++}`, tokens: [] };
}

type Binder = { v: Expr; dom: Expr };

// Opens a pi telescope. `values` replaces the outermost binders, so a
// constructor can be opened against the recursor's own parameters.
function open_telescope(
	ty: Expr,
	values: Expr[] = [],
): { binders: Binder[]; body: Expr } {
	const binders: Binder[] = [];
	let cur = ty;
	let i = 0;
	while (cur.type === "pi") {
		const v = values[i] ?? sentinel();
		binders.push({ v, dom: cur.head });
		cur = app_subst_new_refs(cur.tail, v);
		i++;
	}
	return { binders, body: cur };
}

// Turns a sentinel back into a bound variable. Depth counts the binders
// between here and the pi being built.
function abstract_var(expr: Expr, name: string, depth = 1): Expr {
	if (expr.type === "global") {
		return expr.ident === name
			? { type: "ref", index: depth, tokens: [] }
			: expr;
	} else if (expr.type === "application") {
		return {
			type: "application",
			fun: abstract_var(expr.fun, name, depth),
			value: abstract_var(expr.value, name, depth),
			tokens: [],
		};
	} else if (expr.type === "pi" || expr.type === "lambda") {
		return {
			type: expr.type,
			head: abstract_var(expr.head, name, depth),
			tail: abstract_var(expr.tail, name, depth + 1),
			tokens: [],
		};
	}
	return expr;
}

function close_pi(binders: Binder[], body: Expr): Expr {
	let out = body;
	for (let i = binders.length - 1; i >= 0; i--) {
		const b = binders[i]!;
		out = {
			type: "pi",
			head: b.dom,
			tail: abstract_var(out, (b.v as Expr & { type: "global" }).ident),
			tokens: [],
		};
	}
	return out;
}

function apply(fun: Expr, args: Expr[]): Expr {
	let out = fun;
	for (const arg of args) {
		out = { type: "application", fun: out, value: arg, tokens: [] };
	}
	return out;
}

// The arguments of `X a b c`, left to right.
function spine_args(expr: Expr): Expr[] {
	const args: Expr[] = [];
	let cur = expr;
	while (cur.type === "application") {
		args.unshift(cur.value);
		cur = cur.fun;
	}
	return args;
}

// The parameters are the leading binders every constructor shares and passes
// to the type unchanged; everything after them is an index.
function count_params(globals: Globals, ind: string, ind_binders: Binder[]): number {
	const inductive = globals[ind]!.inductive!;
	// the constructors and their arity are fixed once the inductive is fully
	// declared, so the scan below only ever needs to run once per inductive
	if (inductive.num_params !== undefined) return inductive.num_params;
	const ctors = inductive.constructors;
	let limit = ind_binders.length;
	for (const c of ctors) {
		const { binders } = open_telescope(globals[c]!.ty);
		limit = Math.min(limit, binders.length);
	}
	for (let k = limit; k > 0; k--) {
		const params = ind_binders.slice(0, k).map((b) => b.v);
		const ok = ctors.every((c) => {
			const { body } = open_telescope(globals[c]!.ty, params);
			const args = spine_args(body);
			return (
				args.length >= k &&
				params.every((p, i) => struct_eq(null, args[i]!, p))
			);
		});
		if (ok) {
			inductive.num_params = k;
			return k;
		}
	}
	inductive.num_params = 0;
	return 0;
}

// The types of a constructor's own arguments, past the parameters. Binders are
// opened into opaque values rather than the bare constants derive_recursor uses,
// so that a field mentioning an earlier binder can still be typed.
function ctor_field_doms(ctor_ty: Expr, num_params: number): Expr[] {
	const doms: Expr[] = [];
	let cur = ctor_ty;
	let seen = 0;
	while (cur.type === "pi") {
		if (seen >= num_params) doms.push(cur.head);
		cur = app_subst_new_refs(cur.tail, opaque(cur.head));
		seen += 1;
	}
	return doms;
}

// A Prop may only eliminate into a bigger sort when it is a subsingleton: at
// most one constructor, all of whose non parameter fields are themselves
// proofs. Without this, `Prop.Or.rec` into Type would let a proof decide which
// side it came from, and Prop would stop being irrelevant.
function check_elimination_allowed(
	globals: Globals,
	ind: string,
	ind_sort: Expr,
	motive_sort: Expr,
	num_params: number,
	// what to call the declaration that is trying to eliminate
	where = "",
) {
	if (sort_index(ind_sort) !== 0) return;
	if (sort_index(motive_sort) === 0) return;
	const at = where === "" ? `@rec(${ind})` : where;
	const ctors = globals[ind]!.inductive!.constructors;
	if (ctors.length > 1) {
		throw new Error(
			`${at}: ${ind} is a Prop with ${ctors.length} constructors, so it may only eliminate into Prop`,
		);
	}
	for (const c of ctors) {
		for (const field of ctor_field_doms(globals[c]!.ty, num_params)) {
			let field_sort: Expr;
			try {
				field_sort = type_of(globals, field, {});
			} catch {
				throw new Error(
					`${at}: cannot tell whether '${c}' carries data, so it may only eliminate into Prop`,
				);
			}
			if (sort_index(field_sort) !== 0) {
				throw new Error(
					`${at}: '${c}' carries data, so ${ind} may only eliminate into Prop`,
				);
			}
		}
	}
}

// The recursor for a single, non mutual inductive, at the motive sort the
// declaration asked for.
function derive_recursor(
	globals: Globals,
	ind: string,
	motive_sort: Expr,
): Expr {
	const ind_ty = globals[ind]!.ty;
	const { binders: ind_binders, body: ind_sort } = open_telescope(ind_ty);
	const num_params = count_params(globals, ind, ind_binders);
	const params = ind_binders.slice(0, num_params);
	const indices = ind_binders.slice(num_params);
	const ctors = globals[ind]!.inductive!.constructors;

	check_elimination_allowed(globals, ind, ind_sort, motive_sort, num_params);

	const ind_const: Expr = { type: "global", ident: ind, tokens: [] };
	const param_vars = params.map((b) => b.v);

	// motive : (i.. : I..) -> X p.. i.. -> <sort>
	const major: Binder = {
		v: sentinel(),
		dom: apply(ind_const, [...param_vars, ...indices.map((b) => b.v)]),
	};
	const motive: Binder = {
		v: sentinel(),
		dom: close_pi([...indices, major], motive_sort),
	};
	const motive_at = (idx: Expr[], target: Expr) =>
		apply(motive.v, [...idx, target]);

	const minors: Binder[] = ctors.map((c) => {
		const { binders, body } = open_telescope(globals[c]!.ty, param_vars);
		const fields = binders.slice(num_params);
		const ctor_indices = spine_args(body).slice(num_params);
		const built = apply(
			{ type: "global", ident: c, tokens: [] },
			binders.map((b) => b.v),
		);

		// an induction hypothesis for every field that lands back in X
		const hypotheses: Binder[] = [];
		for (const field of fields) {
			const { binders: inner, body: inner_body } = open_telescope(field.dom);
			const head = head_of(inner_body);
			if (!(head.type === "global" && head.ident === ind)) continue;
			const inner_indices = spine_args(inner_body).slice(num_params);
			hypotheses.push({
				v: sentinel(),
				dom: close_pi(
					inner,
					motive_at(
						inner_indices,
						apply(field.v, inner.map((b) => b.v)),
					),
				),
			});
		}

		return {
			v: sentinel(),
			dom: close_pi(
				[...fields, ...hypotheses],
				motive_at(ctor_indices, built),
			),
		};
	});

	return close_pi(
		[...params, motive, ...minors, ...indices, major],
		motive_at(indices.map((b) => b.v), major.v),
	);
}

// @rec(X): the declared type has to be the recursor for X. The motive's sort is
// read off the declaration rather than derived, since this language has no
// universe polymorphism and states X.rec and X.rec_prop separately.
function check_recursor(globals: Globals, ind: string, ty: Expr, name: string) {
	const target = globals[ind];
	if (!target?.inductive) {
		throw new Error(`@rec(${ind}): ${ind} is not an @inductive type`);
	}
	const { binders: ind_binders } = open_telescope(target.ty);
	const num_params = count_params(globals, ind, ind_binders);

	const { binders } = open_telescope(ty);
	const motive = binders[num_params];
	if (motive === undefined) {
		throw new Error(`@rec(${ind}): '${name}' has no motive`);
	}
	const { body: motive_sort } = open_telescope(motive.dom);
	if (sort_index(motive_sort) < 0) {
		throw new Error(
			`@rec(${ind}): the motive of '${name}' has to end in a sort`,
		);
	}

	const derived = derive_recursor(globals, ind, motive_sort);
	if (!struct_eq(globals, ty, derived)) {
		throw new Error(
			`@rec(${ind}): '${name}' is not the recursor for ${ind}. Expected\n  ${print_expr(derived)}`,
		);
	}
}

// The opaque values a pattern binds, by the id matching substitutes on.
function pattern_vars(
	pat: Expr,
	var_ids: (number | undefined)[],
	out: Set<number>,
) {
	if (pat.type === "def") {
		const id = var_ids[pat.index];
		if (id !== undefined) out.add(id);
	} else if (pat.type === "application") {
		pattern_vars(pat.fun, var_ids, out);
		pattern_vars(pat.value, var_ids, out);
	}
}

// Every recursive call in a rule has to hand a field of the constructor the
// rule matched to the argument being matched on. That is what makes the rules a
// definition rather than an assumption: the matched argument gets structurally
// smaller at every call, so reduction stops, and `f : (n : Nat) -> False` with
// `f Nat.zero := f Nat.zero` is rejected instead of handing back False.
function check_descends(
	globals: Globals,
	name: string,
	body: Expr,
	pos: number,
	smaller: Set<number>,
) {
	const visit = (expr: Expr) => {
		if (expr.type === "application") {
			const head = head_of(expr);
			const args = spine_args(expr);
			if (head.type === "global" && head.ident === name) {
				const arg = pos >= 0 ? args[pos] : undefined;
				if (arg === undefined) {
					throw new Error(
						`@iota '${name}': a recursive call has to pass argument ${
							pos + 1
						}, the one the rules match on`,
					);
				}
				if (arg.type !== "value_with_type" || !smaller.has(arg.id)) {
					throw new Error(
						`@iota '${name}': a recursive call has to pass a field of the constructor its rule matched as argument ${
							pos + 1
						}, so that the recursion gets smaller, but it passes ${print_expr(
							arg,
						)}`,
					);
				}
			} else {
				visit(head);
			}
			for (const a of args) visit(a);
			return;
		}
		if (expr.type === "lambda" || expr.type === "pi") {
			visit(expr.head);
			visit(expr.tail);
			return;
		}
		if (expr.type === "global" && expr.ident === name) {
			throw new Error(
				`@iota '${name}': '${name}' has to be applied to its arguments inside its own rules`,
			);
		}
	};
	visit(body);
}

// The rules of one declaration, checked as a group against the type its @iota
// named, every time one of them arrives. Returns whether they cover that type
// yet: half a set of rules is an assumption, which check_program rejects at the
// end rather than here, since the rules arrive one statement at a time.
function check_iota_rules(globals: Globals, name: string, ind: string): boolean {
	const fail = (why: string): never => {
		throw new Error(`@iota '${name}': ${why}`);
	};
	const clauses = globals[name]!.rules.map((rule) => ({
		rule,
		args: rule.pat_args,
	}));
	for (const c of clauses) {
		if (c.rule.iota !== null && c.rule.iota !== ind) {
			fail(
				`its rules are claimed for both ${c.rule.iota} and ${ind}, but they all match on the same argument`,
			);
		}
	}
	const arity = clauses[0]!.args.length;
	for (const c of clauses) {
		if (c.args.length !== arity) {
			fail("every iota rule has to take the same number of arguments");
		}
	}

	// the argument positions that are something other than a plain variable
	const split = new Set<number>();
	for (const c of clauses) {
		c.args.forEach((a, i) => {
			if (a.type !== "def") split.add(i);
		});
	}
	if (split.size === 0) {
		if (clauses.length > 1) {
			fail("no rule matches on anything, so every one of them applies");
		}
		check_descends(globals, name, clauses[0]!.rule.def, -1, new Set());
		return true;
	}
	if (split.size > 1) {
		fail(
			`the rules match on ${split.size} arguments at once; match one of them and match again inside those rules`,
		);
	}
	const pos = [...split][0]!;

	const ctors = globals[ind]!.inductive!.constructors;
	const seen = new Map<string, number>();
	for (const c of clauses) {
		const head = head_of(c.args[pos]!);
		if (head.type !== "global") {
			return fail(
				`argument ${pos + 1} of a rule has to be a constructor applied to variables, not ${print_expr(
					c.args[pos]!,
				)}`,
			);
		}
		if (!ctors.includes(head.ident)) {
			fail(`${head.ident} is not a constructor of ${ind}`);
		}
		seen.set(head.ident, (seen.get(head.ident) ?? 0) + 1);
	}
	for (const [c, count] of seen) {
		// two rules for one constructor would both fire, and nothing says they
		// agree
		if (count > 1) fail(`${count} rules match ${c}`);
	}

	const { binders: ind_binders, body: ind_sort } = open_telescope(
		globals[ind]!.ty,
	);
	const num_params = count_params(globals, ind, ind_binders);

	for (const c of clauses) {
		// A Prop is irrelevant, so a rule may only look at which constructor a
		// proof used when there was never more than one to choose from.
		let motive_sort: Expr | null = null;
		try {
			motive_sort = type_of(globals, c.rule.ty, {}, []);
		} catch {
			// a rule type we cannot sort cannot be eliminating into anything
		}
		if (motive_sort !== null) {
			check_elimination_allowed(
				globals,
				ind,
				ind_sort,
				motive_sort,
				num_params,
				`@iota '${name}'`,
			);
		}

		// the fields are what the recursion is allowed to descend to: the
		// leading arguments of the pattern are the inductive's parameters,
		// which are the same size as they were
		const smaller = new Set<number>();
		for (const field of spine_args(c.args[pos]!).slice(num_params)) {
			pattern_vars(field, c.rule.var_ids, smaller);
		}
		check_descends(globals, name, c.rule.def, pos, smaller);
	}

	return ctors.every((c) => seen.has(c));
}

function occurs(name: string, expr: Expr): boolean {
	if (expr.type === "global") return expr.ident === name;
	if (expr.type === "application") {
		return occurs(name, expr.fun) || occurs(name, expr.value);
	}
	if (expr.type === "pi" || expr.type === "lambda") {
		return occurs(name, expr.head) || occurs(name, expr.tail);
	}
	if (expr.type === "value_with_type") return occurs(name, expr.ty);
	return false;
}

function head_of(expr: Expr): Expr {
	let cur = expr;
	while (cur.type === "application") cur = cur.fun;
	return cur;
}

// A constructor argument may mention the type being defined only strictly
// positively: either it is an `X ...` itself, or a function *into* `X ...`
// whose own arguments never mention X. X to the left of an arrow would let the
// type contain its own function space, and
//
//   Bad : Type;  Bad.intro : (Bad -> Bad) -> Bad;
//
// is enough to prove False. This is the check that makes @intro worth writing.
function check_strictly_positive(ind: string, arg: Expr) {
	if (!occurs(ind, arg)) return;
	if (arg.type === "pi") {
		if (occurs(ind, arg.head)) {
			throw new Error(
				`${ind} appears to the left of an arrow, which is not strictly positive`,
			);
		}
		check_strictly_positive(ind, arg.tail);
		return;
	}
	const head = head_of(arg);
	if (head.type === "global" && head.ident === ind) {
		// no nested inductives here, so it may not occur in its own arguments
		let cur: Expr = arg;
		while (cur.type === "application") {
			if (occurs(ind, cur.value)) {
				throw new Error(`${ind} appears inside its own arguments`);
			}
			cur = cur.fun;
		}
		return;
	}
	throw new Error(`${ind} appears in a position that is not strictly positive`);
}

// @inductive: the declared type has to end in a sort, so that it is a type
// former at all. @intro(X): every argument strictly positive in X, and the
// whole thing has to land in an X.
function check_inductive_markers(
	globals: Globals,
	stmt: Statement,
	ty: Expr,
	name: string,
) {
	for (const directive of stmt.directives) {
		if (directive.name === "inductive") {
			if (directive.arg !== null) {
				throw new Error("@inductive takes no argument");
			}
			let cur = ty;
			while (cur.type === "pi") cur = cur.tail;
			if (sort_index(cur) < 0) {
				throw new Error(
					`@inductive '${name}' has to end in a sort to be a type`,
				);
			}
		} else if (directive.name === "rec") {
			if (directive.arg === null) {
				throw new Error(
					"@rec needs the type it eliminates, as @rec(Nat)",
				);
			}
			check_recursor(globals, directive.arg, ty, name);
		} else if (directive.name === "intro") {
			const ind = directive.arg;
			if (ind === null) {
				throw new Error(
					"@intro needs the type it builds, as @intro(Nat)",
				);
			}
			if (!globals[ind]?.inductive) {
				throw new Error(`@intro(${ind}): ${ind} is not an @inductive type`);
			}
			let cur = ty;
			while (cur.type === "pi") {
				check_strictly_positive(ind, cur.head);
				cur = cur.tail;
			}
			const head = head_of(cur);
			if (!(head.type === "global" && head.ident === ind)) {
				throw new Error(
					`@intro(${ind}): '${name}' does not build a ${ind}`,
				);
			}
		}
	}
}

export type CheckOptions = {
	// Whether a declaration with no `:=` has to be marked `@axiom`. On for a
	// library, where the trust base is the point; off for the web levels, which
	// are toys whose premises are assumptions by construction.
	require_markers?: boolean;
	// called after every statement with how long it took, for progress and
	// timing. Checking is where the time goes, and a single declaration can
	// account for most of it.
	on_checked?: (stmt: Statement, ms: number) => void;
};

function check_directives(stmt: Statement, opts: CheckOptions) {
	const name = first_ident(stmt.pat).ident;
	for (const directive of stmt.directives) {
		if (PLANNED_DIRECTIVES.includes(directive.name)) {
			throw new Error(
				`@${directive.name} is not checked yet, so '${name}' may not claim it`,
			);
		}
		if (!IMPLEMENTED_DIRECTIVES.includes(directive.name)) {
			throw new Error(`'${name}' has an unknown directive @${directive.name}`);
		}
	}
	// One marker to a statement: what a declaration is, it is once. Markers only
	// ever ask for a check, so stripping every one of them leaves a language
	// that computes the same and assumes what it cannot check.
	if (stmt.directives.length > 1) {
		throw new Error(
			`'${name}' has ${stmt.directives
				.map((d) => `@${d.name}`)
				.join(" and ")}, but a declaration gets exactly one marker`,
		);
	}
	const marker = stmt.directives[0]?.name ?? null;

	if (stmt.pat.type === "application") {
		// a rule: it reduces either way, and @iota(X) asks for the group of
		// them to be checked against X, naming the type the way @intro(Nat)
		// names the type it builds
		if (marker === null) {
			if (opts.require_markers !== false) {
				throw new Error(
					`a rule of '${name}' reduces, so it is an assumption until something checks it: mark it @iota(X) for the type it matches on`,
				);
			}
		} else if (marker !== "iota") {
			throw new Error(
				`a rule of '${name}' may only be @iota(X), not @${marker}`,
			);
		} else if (stmt.directives[0]!.arg === null) {
			throw new Error(
				"@iota needs the type the rule matches on, as @iota(Nat)",
			);
		}
		return;
	}

	if (marker === "iota") {
		throw new Error(
			`@iota marks a rule, so '${name}' may not claim it: a declaration is @axiom, @inductive, @intro(X) or @rec(X)`,
		);
	}

	if (stmt.def === null) {
		if (marker === null && opts.require_markers !== false) {
			throw new Error(
				`'${name}' has no definition, so it is an assumption: mark it @axiom`,
			);
		}
	} else if (marker !== null) {
		throw new Error(
			`'${name}' is defined, so it is not an assumption: drop the @${marker}`,
		);
	}
}

export function check_stmt(
	globals: Globals,
	stmt: Statement,
	opts: CheckOptions = {},
) {
	check_directives(stmt, opts);
	let refs: Expr[] = [];
	let inner_defs: Record<string, Expr> = {};
	let def_names: string[] = [];
	let pat = norm_names(globals, stmt.pat, undefined, def_names);

	let ty: Expr;
	// what the recursor gives at this pattern, for an iota rule
	let pat_ty: Expr | null = null;
	if (stmt.pat.type === "application") {
		// For pattern match rules, ty may reference pattern variables (e.g. `left A a b : A`).
		// Destructure against Any first to populate inner_defs, then resolve ty in that context.
		pat_ty = destructure(
			globals,
			pat,
			{ type: "any", tokens: [] },
			def_names,
			inner_defs,
		);
		ty = reduce_simp_app(globals, norm_names(globals, stmt.ty, inner_defs));
	} else {
		ty = reduce_simp_app(globals, norm_names(globals, stmt.ty));
		// Nothing to destructure. The head of a plain declaration is the name
		// being declared, not a pattern variable, and binding it would put the
		// declaration in scope inside its own definition: `bad : False := bad`
		// would then check, with the body reading as "some proof of False".
	}

	check_is_type(globals, ty, inner_defs);
	check_inductive_markers(globals, stmt, ty, first_ident(stmt.pat).ident);

	// An iota rule does not get to pick its own type: the declaration already fixed
	// what it gives at this pattern. Nothing else compares the two, and a
	// clause that reduced to a term of some other type would take every type in
	// the language with it.
	if (pat_ty !== null && !is_subtype(globals, pat_ty, ty)) {
		throw new Error(
			`At '${print_expr(pat)}': the rule claims ${print_expr(
				ty,
			)}, but ${first_ident(stmt.pat).ident} gives ${print_expr(
				pat_ty,
			)} there`,
		);
	}

	// reduced like the type above: unfolding a global leaves a redex behind, and
	// a binder type inside the value has to end up in the same shape as the
	// declared type it is compared against
	const def = stmt.def
		? reduce_simp_app(globals, norm_names(globals, stmt.def, inner_defs))
		: null;

	if (def) {
		if (!member_of(globals, def, ty, inner_defs)) {
			throw new Error(
				`At '${print_expr(pat)}': ${print_expr(def)} has type ${print_expr(
					type_of(globals, def, inner_defs, refs),
				)}, which is not a member of ${print_expr(ty)}`,
			);
		}
	}

	if (stmt.pat.type === "ident") {
		const first = stmt.pat.ident;
		if (globals[first]) {
			throw new Error(`${first} already defined`);
		}
		globals[first] = { ty, def, rules: [] };
		for (const directive of stmt.directives) {
			if (directive.name === "inductive") {
				globals[first]!.inductive = { constructors: [] };
			} else if (directive.name === "intro") {
				globals[directive.arg!]!.inductive!.constructors.push(first);
			} else if (directive.name === "rec") {
				globals[first]!.rec = directive.arg!;
			}
		}
	} else if (stmt.pat.type === "application") {
		const first = first_ident(stmt.pat).ident;
		if (!def) {
			throw new Error("Matching expressions require a def");
		}
		if (!globals[first]) {
			throw new Error(`${first} not defined`);
		}
		const iota = stmt.directives[0]?.arg ?? null;
		if (iota !== null) {
			if (!globals[iota]?.inductive) {
				throw new Error(
					`@iota(${iota}): ${iota} is not an @inductive type, so there are no constructors to cover`,
				);
			}
			// iota is how an eliminator reduces, so the rules belong to one:
			// everything else is written in terms of a recursor
			if (globals[first]!.rec !== iota) {
				throw new Error(
					`@iota(${iota}): '${first}' is not the recursor for ${iota}, so these are not its iota rules`,
				);
			}
		}
		const var_ids = def_names.map((n) => {
			const v = inner_defs[n];
			return v !== undefined && v.type === "value_with_type"
				? v.id
				: undefined;
		});
		globals[first]!.rules.push({
			pat,
			ty,
			def,
			var_ids,
			iota,
			pat_args: spine_args(pat),
		});
		if (iota !== null) {
			globals[first]!.iota_complete = check_iota_rules(globals, first, iota);
		}
	}
}

export function check_program(
	defs: Globals,
	stmts: Statement[],
	opts: CheckOptions = {},
) {
	for (const stmt of stmts) {
		const started = opts.on_checked ? performance.now() : 0;
		check_stmt(defs, stmt, opts);
		opts.on_checked?.(stmt, performance.now() - started);
	}
	for (const name in defs) {
		const decl = defs[name]!;
		// rules that claimed a type have to cover it: half a set of them
		// reduces on some constructors and assumes the rest
		if (decl.iota_complete === false) {
			throw new Error(
				`@iota '${name}' has no rule for every constructor of the type it matches on, so it is still an assumption`,
			);
		}
	}
}
