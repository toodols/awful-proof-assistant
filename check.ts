// Statements: elaboration of surface syntax and declaration checking.
import { type Global, type Globals, type Sort, type Term, check, check_is_type, infer, new_globals, open_pi, print, unwind } from "./kernel";
import { check_lang_complete, lang_item, register_lang_item } from "./native";
import { normalize, show } from "./debug";
import { check_ctor_positivity, check_iota_rule, derive_and_validate_recursor } from "./inductive";
import { elab_expr } from "./elab";
import type { Directive, Expr, Statement } from "./parser";
import "./native";

export type CheckOptions = {
	require_markers?: boolean;
	on_checked?: (stmt: Statement, ms: number) => void;
	// receives each @debug declaration's name and normalized value; defaults
	// to printing `name = value`
	on_debug?: (name: string, value: string) => void;
};

const MARKERS = ["axiom", "inductive", "intro", "rec"];

function check_decl(
	globals: Globals,
	stmt: Statement,
	opts: CheckOptions,
): void {
	const name = (stmt.pat as Expr & { type: "ident" }).ident;
	if (globals.has(name)) throw new Error(`${name} already defined`);

	// @lang is an extra annotation rather than an alternative marker, so it is
	// counted separately from the "exactly one marker" rule below.
	const lang_directives = stmt.directives.filter((d) => d.name === "lang");
	const debug = stmt.directives.some((d) => d.name === "debug");
	if (debug && stmt.def === null) {
		throw new Error(`@debug needs a definition to print, and ${name} has none`);
	}
	const directives = stmt.directives.filter((d) => d.name !== "lang" && d.name !== "debug");
	if (lang_directives.length > 1) {
		throw new Error(`${name} has more than one @lang`);
	}
	const lang_directive = lang_directives[0] ?? null;
	if (lang_directive !== null && lang_directive.arg === null) {
		throw new Error(`@lang needs the lang item it marks`);
	}
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

	const env = new Map<string, Term>();
	const ty_term = elab_expr(globals, stmt.ty, env);
	check_is_type(globals, ty_term);

	let def_term: Term | null = null;
	if (stmt.def !== null) {
		def_term = elab_expr(globals, stmt.def, env);
		check(globals, def_term, ty_term);
	}

	const g: Global = { ty: ty_term, def: def_term };
	if (lang_directive !== null) {
		register_lang_item(globals, lang_directive.arg!, name, g, marker);
	}
	globals.set(name, g);
	if (debug) {
		const text = show(normalize(globals, def_term!), [], lang_item(globals, "Char.mk"));
		(opts.on_debug ?? ((n, v) => console.log(`${n} = ${v}`)))(name, text);
	}

	if (marker?.name === "inductive") {
		g.is_inductive = true;
		g.ctors = [];
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
		if (lang_item(globals, "Nat") === ind_name && ind.ctors!.length > 2) {
			throw new Error(`@lang(Nat): ${ind_name} may only have two constructors (zero and succ)`);
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
	check_lang_complete(globals);
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

export { new_globals, infer, check } from "./kernel";
export type { Sort, Term, Globals } from "./kernel";
