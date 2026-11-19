// Elaboration: surface syntax into kernel terms.
import { type Globals, type Term, abstract_local, fresh_local } from "./kernel";
import { check_str_literal } from "./native";
import type { Expr } from "./parser";

export function elab_expr(globals: Globals, expr: Expr, env: Map<string, Term>): Term {
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
	if (expr.type === "str_lit") return check_str_literal(expr.value);
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

