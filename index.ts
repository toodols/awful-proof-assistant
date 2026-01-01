import { file, write } from "bun";
import { parse, type Expr, type Statement } from "./parser";

const ast: Statement[] = parse(await file("./practice").text());

type Defs = { [k: string]: { ty: Expr; def: Expr | null } };
const defs: Defs = {};
const error_ty = { type: "error" as const };
defs.Type = { ty: error_ty, def: null };

// (((Eq Nat) ((Nat.Add Nat.zero) (Nat.succ \1))) (Nat.succ ((Nat.Add Nat.zero) \1)))
// (((Eq Nat) ((Nat.Add Nat.zero) (Nat.succ \2))) (Nat.succ ((Nat.Add Nat.zero) \2)))

// For any type, SORRY `type` is a member of `type`
// and SORRY <theorem> is a proof of <theorem>
defs.SORRY = { ty: { type: "sorry" }, def: null };

function type_of(defs: Defs, value: Expr, refs: Expr[] = []): Expr {
	// the type of identifier is its type in defs
	if (value.type === "ident") {
		const def = defs[value.ident];
		if (!def) {
			throw new Error(`${value.ident} not defined`);
		}
		return def.ty;
	} else if (value.type === "lambda") {
		// type of lambda is that but pi
		refs.push(value.head);
		const res = {
			type: "pi",
			head: value.head,
			tail: type_of(defs, value.tail, refs),
		} as const;
		refs.pop();
		return res;
	} else if (value.type === "pi") {
		// type of any Pi expression is just Type
		return { type: "ident", ident: "Type" };
	} else if (value.type === "ref") {
		// only lambda can introduce expressions to ref in type_of so no conflicts with pi
		// however the ref could be referring to another ref
		// in that case we add the ref indices (this is actual black magic)
		const ref = refs[refs.length - value.index]!;
		if (ref) {
			// rename every subref in ref'd to itself + this ref's value.index
			return update_refs(ref, value.index);
		} else {
			return value;
		}
	} else if (value.type === "application") {
		// typeof(((a:Ty) => a) b) = apply(typeof(a), b)
		const fun_ty = type_of(defs, value.fun, refs);
		return apply_type(defs, fun_ty, value.value, refs);
	} else {
		throw new Error(`type_of: ${value.type}`);
	}
}

function update_refs(value: Expr, inc: number): Expr {
	if (value.type === "ref") {
		return { type: "ref", index: value.index + inc };
	} else if (value.type === "application") {
		return {
			type: "application",
			fun: update_refs(value.fun, inc),
			value: update_refs(value.value, inc),
		};
	} else if (value.type === "pi") {
		return {
			type: "pi",
			head: update_refs(value.head, inc),
			tail: update_refs(value.tail, inc),
		};
	} else {
		return value;
	}
}

// rules for replacing refs:
// if the ref's index equals the depth, the value should have its refs combine with the tail's index
// if the ref is less than the depth, it does not change
// if the ref is greater than the depth, it refers outside, and must lose one index
function replace(tail: Expr, value: Expr, depth = 1): Expr {
	if (tail.type === "ref") {
		if (tail.index === depth) {
			return update_refs(value, tail.index - 1);
		} else if (tail.index > depth) {
			return {
				type: "ref",
				index: tail.index - 1,
			};
		} else {
			return tail;
		}
	} else if (tail.type === "application") {
		return {
			type: "application",
			fun: replace(tail.fun, value, depth),
			value: replace(tail.value, value, depth),
		};
	} else if (tail.type === "pi") {
		return {
			type: "pi",
			head: replace(tail.head, value, depth),
			tail: replace(tail.tail, value, depth + 1),
		};
	} else if (tail.type === "ident") {
		return {
			type: "ident",
			ident: tail.ident,
		};
	} else {
		throw new Error(`replace: ${tail.type}`);
	}
}

function print_expr(expr: Expr): string {
	if (expr.type === "lambda") {
		return `(${print_expr(expr.head)} => ${print_expr(expr.tail)})`;
	} else if (expr.type === "pi") {
		return `(${print_expr(expr.head)} -> ${print_expr(expr.tail)})`;
	} else if (expr.type === "application") {
		return `(${print_expr(expr.fun)} ${print_expr(expr.value)})`;
	} else if (expr.type === "ident") {
		return expr.ident;
	} else if (expr.type === "ref") {
		return `\\${expr.index}`;
	} else {
		return "<ERR>";
	}
}

function simp_value(expr: Expr): Expr {
	if (expr.type === "application") {
		if (expr.fun.type === "lambda") {
			return simp_value(replace(expr.fun.tail, simp_value(expr.value)));
		} else {
			return {
				type: "application",
				fun: simp_value(expr.fun),
				value: simp_value(expr.value),
			};
		}
	} else if (expr.type === "lambda") {
		return {
			type: "lambda",
			head: simp_value(expr.head),
			tail: simp_value(expr.tail),
		};
	} else if (expr.type === "pi") {
		return {
			type: "pi",
			head: simp_value(expr.head),
			tail: simp_value(expr.tail),
		};
	} else {
		return expr;
	}
}

function apply_type(defs: Defs, fun: Expr, value: Expr, refs: Expr[]): Expr {
	if (fun.type === "pi") {
		const head = fun.head;
		if (!member_of(defs, value, head, refs)) {
			throw new Error(
				`Type mismatch: ${print_expr(value)} has type ${print_expr(
					type_of(defs, value, refs)
				)}, which is not a member of ${print_expr(head)}`
			);
		}
		// rewrite every ref in tail that references the head
		const tail = fun.tail;
		return simp_value(replace(tail, value));
	} else if (fun.type === "sorry") {
		return value;
	} else {
		throw new Error("don't know how to do this");
	}
}

// Check does expr : ty ?
// Ordinarily we check if
// type_of(expr) is a subset of ty
// but this checker is extremely rudimentary so it only checks if they are equal
function member_of(
	defs: Defs,
	expr: Expr,
	ty: Expr,
	refs: Expr[] = []
): boolean {
	return deep_eq(type_of(defs, expr, refs), ty);
}

// Rename bound variables to use de Bruijn indices
function rename(defs: Defs, expr: Expr, bound: (string | null)[] = []): Expr {
	if (expr.type === "application") {
		return {
			type: "application",
			fun: rename(defs, expr.fun, bound),
			value: rename(defs, expr.value, bound),
		};
	} else if (expr.type === "lambda" || expr.type === "pi") {
		let new_head;
		// if head is a binding, push the binding's ident into bound
		// the binding's ty needs to be rewritten before the binding's ident is pushed into bound
		// after renaming binding.ty, it becomes the new head of the lambda
		if (expr.head.type === "binding") {
			new_head = rename(defs, expr.head.ty, bound);
			bound.push(expr.head.ident);

			// if head is just a type expression, push null into bound
			// null is basically the equivalent of _ : Type bindings. Where the _ technically introduces a new bound variable
		} else {
			new_head = rename(defs, expr.head, bound);
			bound.push(null);
		}

		const ret = {
			type: expr.type,
			head: new_head,
			// as for the tail, it is rewritten after the binding's ident is pushed into bound
			tail: rename(defs, expr.tail, bound),
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
				};
			}
		}
		if (expr.ident in defs) {
			if (defs[expr.ident]!.def !== null) {
				return defs[expr.ident]!.def!;
			}
			return expr;
		} else {
			throw new Error(`${expr.ident} not defined`);
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

function deep_eq(a: Expr, b: Expr): boolean {
	if (a.type === "application") {
		return (
			b.type === a.type &&
			deep_eq(a.fun, b.fun) &&
			deep_eq(a.value, b.value)
		);
	} else if (a.type === "lambda") {
		return (
			b.type === a.type &&
			deep_eq(a.head, b.head) &&
			deep_eq(a.tail, b.tail)
		);
	} else if (a.type === "pi") {
		return (
			b.type === a.type &&
			deep_eq(a.head, b.head) &&
			deep_eq(a.tail, b.tail)
		);
	} else if (a.type === "ident") {
		return b.type === a.type && a.ident === b.ident;
	} else if (a.type === "ref") {
		return b.type === a.type && a.index === b.index;
	} else {
		throw new Error("unreachable");
	}
}

for (const stmt of ast) {
	const ty = rename(defs, stmt.ty);
	const def = stmt.def ? rename(defs, stmt.def) : null;

	if (def) {
		if (member_of(defs, def, ty)) {
			console.log(`Proof '${stmt.ident}' passed`);
		} else {
			throw new Error(
				`Proof '${stmt.ident}' failed: ${print_expr(
					def
				)} has type ${print_expr(
					type_of(defs, def)
				)}, which is not a member of ${print_expr(ty)}`
			);
		}
	}
	defs[stmt.ident] = {
		ty,
		def,
	};
}
