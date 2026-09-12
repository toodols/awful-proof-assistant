import { file, write } from "bun"; // i stop being able to import txt when i remove this for some reason
import { first_ident, type Expr, type Statement, type Token } from "./parser";

type Globals = {
	[k: string]: {
		ty: Expr;
		def: Expr | null;
		rules: { pat: Expr; ty: Expr; def: Expr }[];
		// set by @inductive; constructors are filled in by @intro(...)
		inductive?: { constructors: string[] };
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

// Substitute refs in an expression with known values.
// `ref_vals` holds one opaque value per enclosing binder, innermost last.
function subst_refs(expr: Expr, ref_vals: Expr[]): Expr {
	// console.log(
	// 	`Substituting ${print_expr(expr)} with ${ref_vals.map((e, i) => `${ref_vals.length - i}: ${print_expr(e)}`).join(", ")}`,
	// );
	if (expr.type === "ref") {
		const v = ref_vals[ref_vals.length - expr.index];
		if (v === undefined) {
			throw new Error(`Could not find ref ${expr.index}`);
		}
		return v;
	} else if (expr.type === "application") {
		return {
			type: "application",
			fun: subst_refs(expr.fun, ref_vals),
			value: subst_refs(expr.value, ref_vals),
			tokens: [],
		};
	} else if (expr.type === "pi") {
		const head = subst_refs(expr.head, ref_vals);
		ref_vals.push(opaque(head));

		const val: Expr = {
			type: "pi",
			head: head,
			tail: subst_refs(expr.tail, ref_vals),
			tokens: [],
		};
		ref_vals.pop();
		return val;
	} else if (expr.type === "lambda") {
		return {
			type: "lambda",
			head: subst_refs(expr.head, ref_vals),
			tail: subst_refs(expr.tail, ref_vals),
			tokens: [],
		};
	} else {
		return expr;
	}
}

// destructures a pattern against a type while storing name to their types
// \i = ref[i]
function destructure(
	globals: Globals,
	pat: Expr,
	ty: Expr,
	names: string[],
	destructured: Record<string, Expr>,
	ref_vals: Expr[] = [],
	// the opaque value this position was already given, if the caller made one
	value?: Expr,
): Expr {
	if (pat.type === "def") {
		destructured[names[pat.index]!] = value ?? opaque(ty);
		return ty;
	} else if (pat.type === "application") {
		// pat.fun = ((A => B => C) b) c
		const fun_ty = destructure(
			globals,
			pat.fun,
			{ type: "any", tokens: [] },
			names,
			destructured,
			ref_vals,
		) as Expr & { type: "pi" };

		// fun_ty: B -> C;
		// tail = C;
		// head = B;
		const head = fun_ty.head;
		// the argument and every ref to it in the tail are the same value
		const bound = opaque(head);
		ref_vals.push(bound);
		const tail = reduce_simp_app(subst_refs(fun_ty.tail, ref_vals));
		if (!is_subtype(globals, tail, ty)) {
			throw new Error(
				`expected type ${print_expr(tail)} to be a subtype of ${print_expr(ty)}`,
			);
		}

		// b : B
		destructure(
			globals,
			pat.value,
			head,
			names,
			destructured,
			ref_vals,
			bound,
		);
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

function typeof_app(
	globals: Globals,
	fun: Expr,
	value: Expr,
	inner_defs: Record<string, Expr>,
	// \i : ref[i]
	ref_tys: Expr[],
): Expr {
	if (fun.type === "pi") {
		const head = fun.head;
		if (!member_of(globals, value, head, inner_defs, ref_tys)) {
			throw new Error(
				`Type mismatch: ${print_expr(value)} has type ${print_expr(
					type_of(globals, value, inner_defs, ref_tys),
				)}, which is not a member of ${print_expr(head)}`,
			);
		}
		// rewrite every ref in tail that references the head
		const tail = fun.tail;
		return reduce_simp_app(app_subst_new_refs(tail, value));
	} else if (fun.type === "sorry") {
		return value;
	} else {
		throw new Error(
			`attempt to apply ${print_expr(fun)} with ${print_expr(value)}`,
		);
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
		return reduce_simp_app(
			typeof_app(globals, fun_ty, value.value, inner_defs, ref_tys),
		);
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
	} else {
		throw new Error(`replace: ${tail.type}`);
	}
}

// aka beta reduction. reduces expressions of the form `(A => B) a`
function reduce_simp_app(expr: Expr): Expr {
	if (expr.type === "application") {
		// the function has to be reduced first: in `f a b`, reducing `f a` is
		// what turns the outer application into a redex at all, which is how a
		// global that unfolds to several nested lambdas gets applied to all of
		// its arguments
		const fun = reduce_simp_app(expr.fun);
		const value = reduce_simp_app(expr.value);
		if (fun.type === "lambda") {
			return reduce_simp_app(app_subst_new_refs(fun.tail, value));
		} else if (fun.type === "value_with_type") {
			if (fun.ty.type === "pi") {
				return reduce_simp_app(
					app_subst_new_refs(fun.ty.tail, value),
				);
			} else {
				throw new Error("idk");
			}
		} else {
			return {
				type: "application",
				fun,
				value,
				tokens: [],
			};
		}
	} else if (expr.type === "lambda") {
		return {
			type: "lambda",
			head: reduce_simp_app(expr.head),
			tail: reduce_simp_app(expr.tail),
			tokens: [],
		};
	} else if (expr.type === "pi") {
		return {
			type: "pi",
			head: reduce_simp_app(expr.head),
			tail: reduce_simp_app(expr.tail),
			tokens: [],
		};
	} else {
		return expr;
	}
}

function is_subtype(globals: Globals, subty: Expr, ty: Expr): boolean {
	if (ty.type === "any") return true;
	return struct_eq(globals, subty, ty);
}

function member_of(
	defs: Globals,
	expr: Expr,
	ty: Expr,
	inner_defs: Record<string, Expr> = {},
	ref_tys: Expr[] = [],
): boolean {
	return is_subtype(defs, type_of(defs, expr, inner_defs, ref_tys), ty);
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
function struct_eq(globals: Globals | null, a: Expr, b: Expr): boolean {
	if (globals !== null) {
		try {
			const ty_a = type_of(globals, a);
			const ty_b = type_of(globals, b);
			// use plain structural comparison for the type check to avoid infinite recursion
			if (struct_eq(null, ty_a, ty_b)) {
				const ty_ty = type_of(globals, ty_a);
				if (ty_ty.type === "global" && ty_ty.ident === "Prop") {
					return true;
				}
			}
		} catch {}
	}
	if (a.type === "application") {
		return (
			b.type === "application" &&
			struct_eq(globals, a.fun, b.fun) &&
			struct_eq(globals, a.value, b.value)
		);
	} else if (a.type === "lambda") {
		return (
			b.type === "lambda" &&
			struct_eq(globals, a.head, b.head) &&
			struct_eq(globals, a.tail, b.tail)
		);
	} else if (a.type === "pi") {
		return (
			b.type === "pi" &&
			struct_eq(globals, a.head, b.head) &&
			struct_eq(globals, a.tail, b.tail)
		);
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
const IMPLEMENTED_DIRECTIVES = ["axiom", "inductive", "intro"];
const PLANNED_DIRECTIVES = ["rec"];

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
	if (stmt.def === null && stmt.pat.type === "ident") {
		if (stmt.directives.length === 0 && opts.require_markers !== false) {
			throw new Error(
				`'${name}' has no definition, so it is an assumption: mark it @axiom`,
			);
		}
	} else if (stmt.directives.length > 0) {
		throw new Error(
			`'${name}' is defined, so it is not an assumption: drop the @${stmt.directives[0]!.name}`,
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
	if (stmt.pat.type === "application") {
		// For pattern match rules, ty may reference pattern variables (e.g. `left A a b : A`).
		// Destructure against Any first to populate inner_defs, then resolve ty in that context.
		destructure(globals, pat, { type: "any", tokens: [] }, def_names, inner_defs);
		ty = reduce_simp_app(norm_names(globals, stmt.ty, inner_defs));
	} else {
		ty = reduce_simp_app(norm_names(globals, stmt.ty));
		destructure(globals, pat, ty, def_names, inner_defs);
	}

	check_is_type(globals, ty, inner_defs);
	check_inductive_markers(globals, stmt, ty, first_ident(stmt.pat).ident);

	// reduced like the type above: unfolding a global leaves a redex behind, and
	// a binder type inside the value has to end up in the same shape as the
	// declared type it is compared against
	const def = stmt.def
		? reduce_simp_app(norm_names(globals, stmt.def, inner_defs))
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
		globals[first]!.rules.push({ pat, ty, def });
	}
}

export function check_program(
	defs: Globals,
	stmts: Statement[],
	opts: CheckOptions = {},
) {
	for (const stmt of stmts) {
		check_stmt(defs, stmt, opts);
	}
}
