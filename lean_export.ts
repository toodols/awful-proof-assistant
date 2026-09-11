#!/usr/bin/env bun
/**
 * Exporter from awful-proof-assistant to the Lean 4 export format.
 *
 * There are two spellings of the same format. The flat, line based one is what
 * `lean4export` originally produced and what `trepplein` reads; the line
 * delimited JSON one (format version 3.1.x) is what `lean4export` produces now
 * and what `nanoda` reads. Pick one with --format; both carry the same content,
 * and every line either interns a name, a universe level or an expression under
 * a fresh index, or declares a constant:
 *
 * Text:
 *
 *   <nidx> #NS  <nidx> <string>                name, string component
 *   <nidx> #NI  <nidx> <integer>               name, numeric component
 *   <uidx> #US  <uidx>                         level successor
 *   <uidx> #UP  <nidx>                         level parameter
 *   <eidx> #EV  <integer>                      bound variable, de Bruijn, 0 based
 *   <eidx> #ES  <uidx>                         Sort
 *   <eidx> #EC  <nidx> <uidx>*                 constant with universe arguments
 *   <eidx> #EA  <eidx> <eidx>                  application
 *   <eidx> #EL  <info> <nidx> <eidx> <eidx>    lambda, domain then body
 *   <eidx> #EP  <info> <nidx> <eidx> <eidx>    pi, domain then body
 *          #AX  <nidx> <eidx> <nidx*>          axiom: name, type, universe params
 *          #DEF <nidx> <eidx> <eidx> <nidx*>   definition, with a value
 *
 * JSON, one object per line, the index carried in `in` / `il` / `ie`:
 *
 *   {"in":1,"str":{"pre":0,"str":"Nat"}}            name, string component
 *   {"in":2,"num":{"pre":1,"i":0}}                  name, numeric component
 *   {"il":1,"succ":0}                               level successor
 *   {"il":2,"param":1}                              level parameter
 *   {"ie":0,"bvar":0}                               bound variable
 *   {"ie":1,"sort":1}                               Sort
 *   {"ie":2,"const":{"name":1,"us":[]}}             constant
 *   {"ie":3,"app":{"fn":2,"arg":0}}                 application
 *   {"ie":4,"lam":{...}} / {"ie":5,"forallE":{...}} lambda and pi
 *   {"axiom":{...}} / {"def":{...}}                 declarations
 *
 * Index 0 is pre-populated in both: it is the anonymous name, and the universe
 * zero. The text format additionally starts expression indices at 1.
 *
 * How this language maps onto Lean:
 *
 *   Prop           ->  Sort 0
 *   Type           ->  Sort 1. This language has no universe hierarchy, so
 *                      `Type : Type` holds here but not in Lean; a declaration
 *                      that actually leans on that will be rejected downstream.
 *   `x : T;`       ->  #AX  x : T
 *   `x : T := v;`  ->  #DEF x : T := v
 *   `f a b : T := v;`  a single fully applied rule whose arguments are all
 *                      distinct fresh variables becomes #DEF f := fun a b => v.
 *                      Anything more interesting - several rules, or matching on
 *                      a constructor - has no counterpart in the export format,
 *                      so `f` stays an axiom and the rules are reported as
 *                      skipped.
 *   SORRY          ->  a universe polymorphic axiom `SORRY.{u} : (a : Sort u) -> a`
 *
 * Nothing is universe polymorphic apart from SORRY, and there are no inductive
 * types: this language states every eliminator as an axiom, so inductives,
 * constructors, recursors and Quot are never emitted.
 *
 * Usage:  bun run lean_export.ts [entry] [-o out] [--format text|json]
 *                                [--check] [--header <line>]
 *
 * The format defaults to json for an output path ending in .json, else text.
 */

import { file, write } from "bun";
import { expand } from "./expand";
import { check_program, new_globals } from "./check";
import type { Expr, Statement } from "./parser";

// ---------------------------------------------------------------------------
// Core expressions
//
// The surface AST carries tokens, named binders and unresolved idents. The
// export format wants de Bruijn indices and resolved constants, so we lower to
// this rather than reuse the checker's Expr, whose `value_with_type` nodes have
// already forgotten which pattern variable a value came from.
// ---------------------------------------------------------------------------

export type Level = { k: "num"; n: number } | { k: "param"; name: string };

export type Core =
	| { k: "sort"; level: Level }
	| { k: "const"; name: string; levels: Level[] }
	| { k: "bvar"; idx: number }
	| { k: "app"; fun: Core; arg: Core }
	| { k: "lam"; name: string; dom: Core; body: Core }
	| { k: "pi"; name: string; dom: Core; body: Core };

const SORT_PROP: Core = { k: "sort", level: { k: "num", n: 0 } };
const SORT_TYPE: Core = { k: "sort", level: { k: "num", n: 1 } };

const SORRY = "SORRY";

// ---------------------------------------------------------------------------
// Output formats
//
// The original line based text format and the newer line delimited JSON one
// carry exactly the same information, only spelled differently: `trepplein`
// reads the text one, `nanoda` the JSON one (format version 3.1.x). An emitter
// turns one interned entry into one output line; the interning itself, and so
// the indices, are shared.
// ---------------------------------------------------------------------------

export type Format = "text" | "json";

type Emitter = {
	// index the first expression gets; both formats pre-populate index 0 with
	// the anonymous name and the universe zero, but only the text format also
	// starts expressions at 1
	first_expr: number;
	header(): string[];
	name_str(idx: number, parent: number, part: string): string;
	name_num(idx: number, parent: number, n: number): string;
	level_succ(idx: number, of: number): string;
	level_param(idx: number, name: number): string;
	sort(idx: number, level: number): string;
	constant(idx: number, name: number, levels: number[]): string;
	bvar(idx: number, de_bruijn: number): string;
	app(idx: number, fun: number, arg: number): string;
	binder(
		idx: number,
		k: "lam" | "pi",
		name: number,
		dom: number,
		body: number,
	): string;
	axiom(name: number, ty: number, uparams: number[]): string;
	definition(
		name: number,
		ty: number,
		value: number,
		uparams: number[],
	): string;
};

const text_emitter: Emitter = {
	first_expr: 1,
	header: () => [],
	name_str: (i, pre, part) => `${i} #NS ${pre} ${part}`,
	name_num: (i, pre, n) => `${i} #NI ${pre} ${n}`,
	level_succ: (i, of) => `${i} #US ${of}`,
	level_param: (i, name) => `${i} #UP ${name}`,
	sort: (i, level) => `${i} #ES ${level}`,
	constant: (i, name, us) => `${i} #EC ${[name, ...us].join(" ")}`,
	bvar: (i, n) => `${i} #EV ${n}`,
	app: (i, fun, arg) => `${i} #EA ${fun} ${arg}`,
	// #BD is the default, explicit binder. This language has no implicit or
	// instance binders.
	binder: (i, k, name, dom, body) =>
		`${i} #${k === "lam" ? "EL" : "EP"} #BD ${name} ${dom} ${body}`,
	axiom: (name, ty, us) => ["#AX", name, ty, ...us].join(" "),
	definition: (name, ty, value, us) =>
		["#DEF", name, ty, value, ...us].join(" "),
};

// The version of the JSON format itself, which readers semver check. Everything
// below is shaped for 3.1.x.
const JSON_FORMAT_VERSION = "3.1.0";

const json_emitter: Emitter = {
	first_expr: 0,
	header: () => [
		JSON.stringify({
			meta: {
				exporter: { name: "awful-proof-assistant", version: "0.1.0" },
				format: { version: JSON_FORMAT_VERSION },
				// no Lean produced this, but the fields are not optional
				lean: { githash: "0".repeat(40), version: "4.34.0" },
			},
		}),
	],
	name_str: (i, pre, str) => JSON.stringify({ in: i, str: { pre, str } }),
	name_num: (i, pre, n) => JSON.stringify({ in: i, num: { pre, i: n } }),
	level_succ: (il, succ) => JSON.stringify({ il, succ }),
	level_param: (il, param) => JSON.stringify({ il, param }),
	sort: (ie, sort) => JSON.stringify({ ie, sort }),
	constant: (ie, name, us) => JSON.stringify({ ie, const: { name, us } }),
	bvar: (ie, bvar) => JSON.stringify({ ie, bvar }),
	app: (ie, fn, arg) => JSON.stringify({ ie, app: { fn, arg } }),
	binder: (ie, k, name, type, body) => {
		const binder = { binderInfo: "default", body, name, type };
		return JSON.stringify(
			k === "lam" ? { ie, lam: binder } : { ie, forallE: binder },
		);
	},
	axiom: (name, ty, us) =>
		JSON.stringify({
			axiom: { name, levelParams: us, type: ty, isUnsafe: false },
		}),
	definition: (name, ty, value, us) =>
		JSON.stringify({
			def: {
				name,
				levelParams: us,
				type: ty,
				value,
				// nothing here is recursive, so every definition unfolds eagerly
				hints: "abbrev",
				safety: "safe",
			},
		}),
};

const emitters: Record<Format, Emitter> = {
	text: text_emitter,
	json: json_emitter,
};

// ---------------------------------------------------------------------------
// Writer: interns names, levels and expressions, emits declaration lines
// ---------------------------------------------------------------------------

class Writer {
	lines: string[];
	private names = new Map<string, number>();
	private levels = new Map<string, number>();
	private exprs = new Map<string, number>();
	private next_name = 1;
	private next_level = 1;
	private next_expr: number;

	constructor(private out: Emitter) {
		this.lines = out.header();
		this.next_expr = out.first_expr;
	}

	// `key` identifies an entry across formats; `line` spells it out, once the
	// entry turns out to be new and has been given an index.
	private intern(
		cache: Map<string, number>,
		key: string,
		line: (idx: number) => string,
		alloc: () => number,
	): number {
		const hit = cache.get(key);
		if (hit !== undefined) return hit;
		const idx = alloc();
		cache.set(key, idx);
		this.lines.push(line(idx));
		return idx;
	}

	// Interns a dotted identifier as a hierarchical Lean name.
	name(ident: string): number {
		if (ident === "") return 0;
		let parent = 0;
		for (const part of ident.split(".")) {
			if (part === "") {
				throw new Error(`empty name component in '${ident}'`);
			}
			const pre = parent;
			const alloc = () => this.next_name++;
			parent = /^[0-9]+$/.test(part)
				? this.intern(
						this.names,
						`NI ${pre} ${part}`,
						(i) => this.out.name_num(i, pre, +part),
						alloc,
					)
				: this.intern(
						this.names,
						`NS ${pre} ${part}`,
						(i) => this.out.name_str(i, pre, part),
						alloc,
					);
		}
		return parent;
	}

	level(level: Level): number {
		if (level.k === "param") {
			const name = this.name(level.name);
			return this.intern(
				this.levels,
				`UP ${name}`,
				(i) => this.out.level_param(i, name),
				() => this.next_level++,
			);
		}
		if (level.n < 0) throw new Error(`negative universe level ${level.n}`);
		// index 0 is level zero, already present
		let idx = 0;
		for (let i = 0; i < level.n; i++) {
			const of = idx;
			idx = this.intern(
				this.levels,
				`US ${of}`,
				(j) => this.out.level_succ(j, of),
				() => this.next_level++,
			);
		}
		return idx;
	}

	expr(e: Core): number {
		let key: string;
		let line: (idx: number) => string;
		if (e.k === "sort") {
			const level = this.level(e.level);
			key = `ES ${level}`;
			line = (i) => this.out.sort(i, level);
		} else if (e.k === "const") {
			const name = this.name(e.name);
			const us = e.levels.map((l) => this.level(l));
			key = `EC ${[name, ...us].join(" ")}`;
			line = (i) => this.out.constant(i, name, us);
		} else if (e.k === "bvar") {
			const n = e.idx;
			key = `EV ${n}`;
			line = (i) => this.out.bvar(i, n);
		} else if (e.k === "app") {
			const fun = this.expr(e.fun);
			const arg = this.expr(e.arg);
			key = `EA ${fun} ${arg}`;
			line = (i) => this.out.app(i, fun, arg);
		} else {
			// children first: an index may only refer to a smaller index
			const k = e.k;
			const name = this.name(e.name);
			const dom = this.expr(e.dom);
			const body = this.expr(e.body);
			key = `${k} ${name} ${dom} ${body}`;
			line = (i) => this.out.binder(i, k, name, dom, body);
		}
		return this.intern(this.exprs, key, line, () => this.next_expr++);
	}

	axiom(name: string, ty: Core, uparams: string[] = []) {
		this.lines.push(
			this.out.axiom(
				this.name(name),
				this.expr(ty),
				uparams.map((u) => this.name(u)),
			),
		);
	}

	definition(name: string, ty: Core, value: Core, uparams: string[] = []) {
		this.lines.push(
			this.out.definition(
				this.name(name),
				this.expr(ty),
				this.expr(value),
				uparams.map((u) => this.name(u)),
			),
		);
	}
}

// ---------------------------------------------------------------------------
// Resolution: surface Expr -> Core
// ---------------------------------------------------------------------------

type Global = { name: string; ty: Core };

type Env = {
	globals: Map<string, Global>;
	// names already written out, used to catch forward references
	emitted: Set<string>;
	uses_sorry: boolean;
};

// The universe level `u` such that `ty : Sort u`. Only used to instantiate
// SORRY at a use site: it walks to the head of the type and reads the codomain
// off that constant's declared type, which is enough for a language whose only
// sorts are Prop and Type.
function sort_level_of(env: Env, ty: Core): Level {
	let cur = ty;
	// a pi into Prop is itself a Prop, by impredicativity
	while (cur.k === "pi") cur = cur.body;
	if (cur.k === "sort") {
		// `ty` is itself a sort, so it lives one level up
		return cur.level.k === "num"
			? { k: "num", n: cur.level.n + 1 }
			: { k: "num", n: 1 };
	}
	let head: Core = cur;
	while (head.k === "app") head = head.fun;
	if (head.k === "const") {
		let codomain = env.globals.get(head.name)?.ty;
		while (codomain?.k === "pi") codomain = codomain.body;
		if (codomain?.k === "sort") return codomain.level;
	}
	return { k: "num", n: 1 };
}

// `bound` is the de Bruijn context, innermost last. Anonymous binders are
// pushed as null so that no ident can ever resolve to them.
function resolve(env: Env, expr: Expr, bound: (string | null)[]): Core {
	if (expr.type === "ident") {
		for (let i = bound.length - 1; i >= 0; i--) {
			if (bound[i] === expr.ident) {
				return { k: "bvar", idx: bound.length - 1 - i };
			}
		}
		if (expr.ident === "Type") return SORT_TYPE;
		if (expr.ident === "Prop") return SORT_PROP;
		if (expr.ident === SORRY) {
			// a bare SORRY with nothing applied; default to the Type level
			env.uses_sorry = true;
			return { k: "const", name: SORRY, levels: [{ k: "num", n: 1 }] };
		}
		if (expr.ident === "Any") {
			throw new Error("`Any` has no counterpart in Lean");
		}
		if (!env.globals.has(expr.ident)) {
			throw new Error(`${expr.ident} not defined`);
		}
		if (!env.emitted.has(expr.ident)) {
			throw new Error(
				`${expr.ident} is used before it is declared in the export ` +
					`(a pattern rule's body may only mention earlier declarations)`,
			);
		}
		return { k: "const", name: expr.ident, levels: [] };
	} else if (expr.type === "application") {
		const arg = resolve(env, expr.value, bound);
		// SORRY is the one universe polymorphic constant we emit, so its level
		// argument has to be read off whatever it is applied to.
		if (
			expr.fun.type === "ident" &&
			expr.fun.ident === SORRY &&
			!bound.includes(SORRY)
		) {
			env.uses_sorry = true;
			return {
				k: "app",
				fun: {
					k: "const",
					name: SORRY,
					levels: [sort_level_of(env, arg)],
				},
				arg,
			};
		}
		return { k: "app", fun: resolve(env, expr.fun, bound), arg };
	} else if (expr.type === "lambda" || expr.type === "pi") {
		// `(x : A) -> B` binds x in B; a bare `A -> B` still occupies a slot
		const binding = expr.head.type === "binding" ? expr.head : null;
		const dom = resolve(env, binding ? binding.ty : expr.head, bound);
		bound.push(binding ? binding.ident : null);
		const body = resolve(env, expr.tail, bound);
		const name = bound[bound.length - 1] ?? "_";
		bound.pop();
		return { k: expr.type === "lambda" ? "lam" : "pi", name, dom, body };
	} else if (expr.type === "binding") {
		throw new Error("found a binding outside lambda or pi");
	}
	throw new Error(`cannot export ${expr.type} expression`);
}

// ---------------------------------------------------------------------------
// Declarations
// ---------------------------------------------------------------------------

type Decl = {
	name: string;
	ty: Expr;
	def: Expr | null;
	// pattern rules attached to this name, in source order
	rules: { args: Expr[]; def: Expr | null }[];
};

export type ExportResult = {
	text: string;
	axioms: number;
	definitions: number;
	skipped: { name: string; reason: string }[];
};

// Splits `f a b` into its head ident and its arguments, left to right.
function spine(expr: Expr): { head: string; args: Expr[] } {
	const args: Expr[] = [];
	let cur = expr;
	while (cur.type === "application") {
		args.unshift(cur.value);
		cur = cur.fun;
	}
	if (cur.type !== "ident") throw new Error("pattern head is not an ident");
	return { head: cur.ident, args };
}

export function export_to_lean(
	statements: Statement[],
	opts: { header?: string; format?: Format } = {},
): ExportResult {
	// Pass 1: collect declarations in source order and hang every pattern rule
	// off the declaration it refines.
	const decls: Decl[] = [];
	const by_name = new Map<string, Decl>();
	for (const stmt of statements) {
		if (stmt.pat.type === "ident") {
			const name = stmt.pat.ident;
			if (by_name.has(name)) throw new Error(`${name} already defined`);
			const decl: Decl = { name, ty: stmt.ty, def: stmt.def, rules: [] };
			decls.push(decl);
			by_name.set(name, decl);
		} else {
			const { head, args } = spine(stmt.pat);
			const decl = by_name.get(head);
			if (!decl) throw new Error(`${head} not defined`);
			decl.rules.push({ args, def: stmt.def });
		}
	}

	// Pass 2: resolve and emit. Source order is already dependency order,
	// because the language has no forward references.
	const w = new Writer(emitters[opts.format ?? "text"]);
	const env: Env = {
		globals: new Map(),
		emitted: new Set(),
		uses_sorry: false,
	};
	const skipped: { name: string; reason: string }[] = [];
	let axioms = 0;
	let definitions = 0;

	for (const decl of decls) {
		const ty = resolve(env, decl.ty, []);
		env.globals.set(decl.name, { name: decl.name, ty });

		let value = decl.def ? resolve(env, decl.def, []) : null;

		if (decl.rules.length > 0) {
			if (value !== null) {
				skipped.push({
					name: decl.name,
					reason: "it already has a definition, so its rules add nothing",
				});
			} else {
				const [lowered, reason] = lower_rules(env, decl, ty);
				if (lowered) value = lowered;
				else skipped.push({ name: decl.name, reason: reason! });
			}
		}

		if (env.uses_sorry && !env.emitted.has(SORRY)) {
			// SORRY.{u} : (a : Sort u) -> a
			env.emitted.add(SORRY);
			w.axiom(
				SORRY,
				{
					k: "pi",
					name: "a",
					dom: { k: "sort", level: { k: "param", name: "u" } },
					body: { k: "bvar", idx: 0 },
				},
				["u"],
			);
			axioms++;
		}

		if (value) {
			w.definition(decl.name, ty, value);
			definitions++;
		} else {
			w.axiom(decl.name, ty);
			axioms++;
		}
		env.emitted.add(decl.name);
	}

	const lines = opts.header ? [opts.header, ...w.lines] : w.lines;
	return { text: lines.join("\n") + "\n", axioms, definitions, skipped };
}

// Turns `f a b : T := v` into `fun (a : A) (b : B) => v`, taking the binder
// types off the front of `f`'s declared pi type. Only a single rule whose
// arguments are all distinct fresh variables can be lowered this way; real
// pattern matching has no counterpart in the export format.
function lower_rules(
	env: Env,
	decl: Decl,
	ty: Core,
): [Core | null, string | null] {
	if (decl.rules.length > 1) {
		return [
			null,
			`${decl.rules.length} pattern rules cannot become one definition`,
		];
	}
	const rule = decl.rules[0]!;
	if (!rule.def) return [null, "the pattern rule has no body"];

	const binders: { name: string; dom: Core }[] = [];
	let rest = ty;
	for (const arg of rule.args) {
		if (arg.type !== "ident") {
			return [null, "a pattern argument is not a variable"];
		}
		if (env.globals.has(arg.ident)) {
			return [null, `it matches on the constructor '${arg.ident}'`];
		}
		if (binders.some((b) => b.name === arg.ident)) {
			return [null, `the pattern variable '${arg.ident}' is repeated`];
		}
		if (rest.k !== "pi") {
			return [
				null,
				`it has more arguments than ${decl.name}'s type has binders`,
			];
		}
		binders.push({ name: arg.ident, dom: rest.dom });
		rest = rest.body;
	}

	const bound: (string | null)[] = binders.map((b) => b.name);
	let body = resolve(env, rule.def, bound);
	for (let i = binders.length - 1; i >= 0; i--) {
		body = { k: "lam", name: binders[i]!.name, dom: binders[i]!.dom, body };
	}
	return [body, null];
}

// ---------------------------------------------------------------------------
// CLI
// ---------------------------------------------------------------------------

if (import.meta.main) {
	const argv = process.argv.slice(2);
	let entry = "./defs/main.txt";
	let out: string | null = null;
	let header: string | undefined;
	let format: Format | null = null;
	let check = false;
	let entry_seen = false;

	for (let i = 0; i < argv.length; i++) {
		const a = argv[i]!;
		if (a === "-o" || a === "--out") {
			out = argv[++i]!;
		} else if (a === "--header") {
			header = argv[++i]!;
		} else if (a === "--format") {
			const f = argv[++i];
			if (f !== "text" && f !== "json") {
				console.error("--format must be text or json");
				process.exit(2);
			}
			format = f;
		} else if (a === "--check") {
			check = true;
		} else if (a === "-h" || a === "--help") {
			console.log(
				"usage: bun run lean_export.ts [entry] [-o out] " +
					"[--format text|json] [--check] [--header <line>]",
			);
			process.exit(0);
		} else if (a.startsWith("-")) {
			console.error(`unknown option ${a}`);
			process.exit(2);
		} else if (!entry_seen) {
			entry = a;
			entry_seen = true;
		} else {
			console.error(`unexpected argument ${a}`);
			process.exit(2);
		}
	}

	const statements = await expand(entry, async (p) => await file(p).text());

	if (check) {
		check_program(new_globals(), statements);
	}

	// a .json output path picks the JSON format on its own
	const result = export_to_lean(statements, {
		header,
		format: format ?? (out?.endsWith(".json") ? "json" : "text"),
	});

	if (out) {
		await write(out, result.text);
		console.error(
			`wrote ${out}: ${result.definitions} definitions, ${result.axioms} axioms`,
		);
	} else {
		process.stdout.write(result.text);
	}
	for (const s of result.skipped) {
		console.error(`warning: ${s.name} exported as an axiom, ${s.reason}`);
	}
}
