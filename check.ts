import { file, write } from "bun"; // i stop being able to import txt when i remove this for some reason
import { first_ident, type Expr, type Statement, type Token } from "./parser";

type Globals = {
	[k: string]: {
		ty: Expr;
		def: Expr | null;
		rules: { pat: Expr; ty: Expr; def: Expr }[];
	};
};
const error_ty = { type: "error" as const, tokens: [] as Token[] };

export function new_globals() {
	const globals: Globals = {};

	globals.Type = { ty: error_ty, def: null, rules: [] };
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
		return `(_ : ${print_expr(expr.ty)})`;
	} else {
		return `<${expr.type} is err>`;
	}
}

// Substitute refs in an expression with known values
function subst_refs(expr: Expr, ref_vals: Expr[]): Expr {
	// console.log(
	// 	`Substituting ${print_expr(expr)} with ${ref_vals.map((e, i) => `${ref_vals.length - i}: ${print_expr(e)}`).join(", ")}`,
	// );
	if (expr.type === "ref") {
		const v = ref_vals[ref_vals.length - expr.index];
		if (v === undefined) {
			throw new Error(`Could not find ref ${expr.index}`);
		}
		return { type: "value_with_type", ty: v, tokens: [] };
	} else if (expr.type === "application") {
		return {
			type: "application",
			fun: subst_refs(expr.fun, ref_vals),
			value: subst_refs(expr.value, ref_vals),
			tokens: [],
		};
	} else if (expr.type === "pi") {
		const head = subst_refs(expr.head, ref_vals);
		ref_vals.push(head);

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
): Expr {
	if (pat.type === "def") {
		destructured[names[pat.index]!] = {
			type: "value_with_type",
			ty,
			tokens: [],
		};
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
		ref_vals.push(head);
		const tail = reduce_simp_app(subst_refs(fun_ty.tail, ref_vals));
		if (!is_subtype(tail, ty)) {
			throw new Error(
				`expected type ${print_expr(tail)} to be a subtype of ${print_expr(ty)}`,
			);
		}

		// b : B
		destructure(globals, pat.value, head, names, destructured, ref_vals);
		// DO NOT POP REFVALS
		return tail;
	} else if (pat.type === "global") {
		const var_ty = globals[pat.ident]!.ty;
		if (!is_subtype(var_ty, ty)) {
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
		// type of any Pi expression is just Type
		return { type: "global", ident: "Type", tokens: [] };
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
		if (expr.fun.type === "lambda") {
			return reduce_simp_app(
				app_subst_new_refs(expr.fun.tail, reduce_simp_app(expr.value)),
			);
		} else if (expr.fun.type === "value_with_type") {
			if (expr.fun.ty.type === "pi") {
				return reduce_simp_app(
					app_subst_new_refs(
						expr.fun.ty.tail,
						reduce_simp_app(expr.value),
					),
				);
			} else {
				throw new Error("idk");
			}
		} else {
			return {
				type: "application",
				fun: reduce_simp_app(expr.fun),
				value: reduce_simp_app(expr.value),
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

function is_subtype(subty: Expr, ty: Expr): boolean {
	if (ty.type === "any") return true;
	return struct_eq(subty, ty);
}

function member_of(
	defs: Globals,
	expr: Expr,
	ty: Expr,
	inner_defs: Record<string, Expr> = {},
	ref_tys: Expr[] = [],
): boolean {
	return is_subtype(type_of(defs, expr, inner_defs, ref_tys), ty);
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

// Whether two expressions are structurally equal
function struct_eq(a: Expr, b: Expr): boolean {
	if (a.type === "application") {
		return (
			b.type === a.type &&
			struct_eq(a.fun, b.fun) &&
			struct_eq(a.value, b.value)
		);
	} else if (a.type === "lambda") {
		return (
			b.type === a.type &&
			struct_eq(a.head, b.head) &&
			struct_eq(a.tail, b.tail)
		);
	} else if (a.type === "pi") {
		return (
			b.type === a.type &&
			struct_eq(a.head, b.head) &&
			struct_eq(a.tail, b.tail)
		);
	} else if (a.type === "global") {
		return b.type === a.type && a.ident === b.ident;
	} else if (a.type === "ref") {
		return b.type === a.type && a.index === b.index;
	} else {
		throw new Error(`unreachable: ${a.type}`);
	}
}

export function check_stmt(globals: Globals, stmt: Statement) {
	const ty = reduce_simp_app(norm_names(globals, stmt.ty));
	let refs: Expr[] = [];
	let inner_defs: Record<string, Expr> = {};
	let def_names: string[] = [];
	let pat = norm_names(globals, stmt.pat, undefined, def_names);
	destructure(globals, pat, ty, def_names, inner_defs);
	const def = stmt.def ? norm_names(globals, stmt.def, inner_defs) : null;

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

export function check_program(defs: Globals, stmts: Statement[]) {
	for (const stmt of stmts) {
		check_stmt(defs, stmt);
	}
}
