// Native values: lang items, and the numerals and strings they stand for.
import { type Global, type Globals, type Local, type Term, apply, check, defeq, hooks, open_pi, unwind, whnf } from "./kernel";
import type { Directive } from "./parser";

// Lang items: which declaration in this program each @lang(Item) named. The
// items are the things the checker needs to know by role rather than by
// name, so a program picks its own names for them. Kept out of the Globals
// map itself (a plain `Map<string, Global>`, which every caller already
// constructs and passes around) so the exported type does not have to grow a
// field nothing else needs to know about.
export const LANG_ITEMS = [
	"Nat",
	"Nat.zero",
	"Nat.succ",
	"Nat.add",
	"Nat.mul",
	"Bool.true",
	"Bool.false",
	"Nat.ble",
	"String",
	"String.nil",
	"String.cons",
	"Char.mk",
];

export const lang_registry = new WeakMap<Globals, Map<string, string>>();

export function lang_items(globals: Globals): Map<string, string> {
	let items = lang_registry.get(globals);
	if (!items) {
		items = new Map();
		lang_registry.set(globals, items);
	}
	return items;
}

export function lang_item(globals: Globals, item: string): string | undefined {
	return lang_registry.get(globals)?.get(item);
}

export function need_lang_item(globals: Globals, item: string, why: string): string {
	const name = lang_item(globals, item);
	if (name === undefined) throw new Error(`${why} needs an @lang(${item}) declaration in scope`);
	return name;
}

// A string, spelled out one layer: String.cons of its first character and
// the rest (still a native string), or String.nil when empty, reduced to
// whatever those declarations are definitions of. A character is Char.mk
// applied to its code point and a proof that it is valid; the proof is an
// opaque local of exactly the right Prop, which proof irrelevance makes
// indistinguishable from any other.
export function unfold_str(globals: Globals, s: string): Term {
	if (s === "") {
		return whnf(globals, {
			k: "global",
			name: need_lang_item(globals, "String.nil", "a string"),
		});
	}
	const cons = need_lang_item(globals, "String.cons", "a string");
	const mk = need_lang_item(globals, "Char.mk", "a string");
	const code = s.codePointAt(0)!;
	const { locals } = open_pi(globals.get(mk)!.ty, 2, [{ k: "nat", n: BigInt(code) }]);
	const ch = apply({ k: "global", name: mk }, locals);
	const rest: Term = { k: "str", s: s.slice(code > 0xffff ? 2 : 1) };
	return whnf(globals, apply({ k: "global", name: cons }, [ch, rest]));
}

// A `nat`/`str` value, spelled out as the constructor application it stands
// for - one layer only (its own fields stay `nat`/`str` too), so recursor
// matching can treat a native value exactly like an ordinary constructor
// application without knowing natives exist.
export function native_ctor_spine(
	globals: Globals,
	ind_name: string,
	target: Term,
): { head: Term; args: Term[] } | null {
	if (target.k === "str") return unwind(unfold_str(globals, target.s));
	if (target.k !== "nat") return null;
	if (lang_item(globals, "Nat") !== ind_name) return null;
	const zero = lang_item(globals, "Nat.zero");
	const succ = lang_item(globals, "Nat.succ");
	if (!zero || !succ) return null;
	if (target.n <= 0n) return { head: { k: "global", name: zero }, args: [] };
	return {
		head: { k: "global", name: succ },
		args: [{ k: "nat", n: target.n - 1n }],
	};
}

// @lang(Nat.zero) takes no arguments; @lang(Nat.succ) takes exactly one,
// directly (not behind a further binder) the type itself. That is exactly a
// Peano numeral's shape, which native `nat` values stand in for one layer at
// a time.
export function validate_nat_ctor(item: string, ind_name: string, ty: Term): "zero" | "succ" {
	const { locals } = open_pi(ty, Infinity);
	if (item === "Nat.zero") {
		if (locals.length !== 0) {
			throw new Error(`@lang(Nat.zero) has to take no arguments`);
		}
		return "zero";
	}
	if (locals.length !== 1) {
		throw new Error(`@lang(Nat.succ) has to take exactly one ${ind_name} field`);
	}
	const head = unwind((locals[0] as Local).ty).head;
	if (!(head.k === "global" && head.name === ind_name)) {
		throw new Error(`@lang(Nat.succ)'s field has to be ${ind_name} itself`);
	}
	return "succ";
}

// Checks a declaration is shaped the way its @lang item needs, then records
// it. `marker` is the declaration's one marker, if any.
export function register_lang_item(
	globals: Globals,
	item: string,
	name: string,
	g: Global,
	marker: Directive | null,
): void {
	if (!LANG_ITEMS.includes(item)) {
		throw new Error(`@lang does not know ${item}, only ${LANG_ITEMS.join(", ")}`);
	}
	const items = lang_items(globals);
	const existing = items.get(item);
	if (existing !== undefined) throw new Error(`@lang(${item}) is already ${existing}`);

	const global_of = (n: string): Term => ({ k: "global", name: n });
	const same_type = (a: Term, b: Term, what: string) => {
		if (!defeq(globals, a, b)) throw new Error(`@lang(${item}) ${what}`);
	};
	switch (item) {
		case "Nat":
			if (marker?.name !== "inductive") {
				throw new Error(`@lang(Nat) may only mark an @inductive declaration`);
			}
			break;
		case "Nat.zero":
		case "Nat.succ": {
			const nat = need_lang_item(globals, "Nat", `@lang(${item})`);
			if (marker?.name !== "intro" || marker.arg !== nat) {
				throw new Error(`@lang(${item}) may only mark an @intro(${nat}) constructor`);
			}
			g.lang_role = validate_nat_ctor(item, nat, g.ty);
			break;
		}
		case "Nat.add":
		case "Nat.mul": {
			const nat = global_of(need_lang_item(globals, "Nat", `@lang(${item})`));
			const n_ty: Term = { k: "pi", dom: nat, body: nat };
			same_type(g.ty, { k: "pi", dom: nat, body: n_ty }, `has to be ${lang_item(globals, "Nat")} -> ${lang_item(globals, "Nat")} -> ${lang_item(globals, "Nat")}`);
			if (g.def === null) throw new Error(`@lang(${item}) needs a definition`);
			// the native fast path replaces unfolding the definition, so make
			// sure the definition really is the operation: spot-check it
			const add = item === "Nat.add";
			for (const [x, y] of [[0n, 0n], [0n, 3n], [4n, 0n], [2n, 3n], [5n, 4n]] as const) {
				const got = whnf(globals, apply(g.def, [{ k: "nat", n: x }, { k: "nat", n: y }]));
				const want = add ? x + y : x * y;
				if (!(got.k === "nat" && got.n === want)) {
					throw new Error(`@lang(${item}): ${name} ${x} ${y} does not compute to ${want}`);
				}
			}
			g.lang_role = add ? "add" : "mul";
			break;
		}
		case "Bool.true":
		case "Bool.false":
			// the two results a native Nat.ble hands back; any type will do, so
			// long as they share it
			if (item === "Bool.false") {
				const t = need_lang_item(globals, "Bool.true", `@lang(${item})`);
				same_type(g.ty, globals.get(t)!.ty, `has to have the same type as ${t}`);
			}
			break;
		case "Nat.ble": {
			const nat = global_of(need_lang_item(globals, "Nat", `@lang(${item})`));
			const yes = need_lang_item(globals, "Bool.true", `@lang(${item})`);
			const no = need_lang_item(globals, "Bool.false", `@lang(${item})`);
			const n_ty: Term = { k: "pi", dom: nat, body: globals.get(yes)!.ty };
			same_type(g.ty, { k: "pi", dom: nat, body: n_ty }, `has to be Nat -> Nat -> ${yes}'s type`);
			if (g.def === null) throw new Error(`@lang(${item}) needs a definition`);
			for (const [x, y] of [[0n, 0n], [0n, 3n], [3n, 0n], [2n, 3n], [3n, 2n], [4n, 4n]] as const) {
				const got = whnf(globals, apply(g.def, [{ k: "nat", n: x }, { k: "nat", n: y }]));
				const want = x <= y ? yes : no;
				if (!(got.k === "global" && got.name === want)) {
					throw new Error(`@lang(${item}): ${name} ${x} ${y} does not compute to ${want}`);
				}
			}
			g.lang_role = "ble";
			break;
		}
		case "String": {
			const w = whnf(globals, g.ty);
			if (!(w.k === "sort" && w.s === 1)) {
				throw new Error(`@lang(String) has to be a Type`);
			}
			break;
		}
		case "String.nil": {
			const str = need_lang_item(globals, "String", `@lang(${item})`);
			same_type(g.ty, global_of(str), `has to be a ${str}`);
			break;
		}
		case "String.cons": {
			const str = global_of(need_lang_item(globals, "String", `@lang(${item})`));
			const { locals, body } = open_pi(g.ty, Infinity);
			if (locals.length !== 2) {
				throw new Error(`@lang(String.cons) has to take a character and a string`);
			}
			same_type((locals[1] as Local).ty, str, `has to take the string as its second argument`);
			same_type(body, str, `has to give a string`);
			break;
		}
		case "Char.mk": {
			const nat = global_of(need_lang_item(globals, "Nat", `@lang(${item})`));
			const { locals } = open_pi(g.ty, Infinity);
			if (locals.length !== 2) {
				throw new Error(`@lang(Char.mk) has to take a code point and a proof it is valid`);
			}
			same_type((locals[0] as Local).ty, nat, `has to take a code point as its first argument`);
			break;
		}
	}
	items.set(item, name);
}

export function check_str_literal(value: string): Term {
	for (const ch of value) {
		const code = ch.codePointAt(0)!;
		if (code > 0x10ffff || (code >= 0xd800 && code <= 0xdfff)) {
			throw new Error(`U+${code.toString(16).toUpperCase()} is not a valid character`);
		}
	}
	return { k: "str", s: value };
}

export function check_lang_complete(globals: Globals): void {
	if (lang_item(globals, "Nat") !== undefined) {
		for (const item of ["Nat.zero", "Nat.succ"]) {
			if (lang_item(globals, item) === undefined) {
				throw new Error(`@lang(Nat) needs an @lang(${item}) constructor`);
			}
		}
	}
}

hooks.reduce = (globals, role, args) => {
	if (role === "zero") return apply({ k: "nat", n: 0n }, args);
	if (role === "succ" && args.length >= 1) {
		const n = whnf(globals, args[0]!);
		if (n.k === "nat") return apply({ k: "nat", n: n.n + 1n }, args.slice(1));
		return null;
	}
	if ((role === "add" || role === "mul" || role === "ble") && args.length >= 2) {
		const a = whnf(globals, args[0]!);
		const b = whnf(globals, args[1]!);
		if (a.k !== "nat" || b.k !== "nat") return null;
		if (role === "ble") {
			const name = lang_item(globals, a.n <= b.n ? "Bool.true" : "Bool.false")!;
			return apply({ k: "global", name }, args.slice(2));
		}
		return apply({ k: "nat", n: role === "add" ? a.n + b.n : a.n * b.n }, args.slice(2));
	}
	return null;
};
hooks.spine = native_ctor_spine;
hooks.unfold = (globals, t) => (t.k === "str" ? unfold_str(globals, t.s) : null);
hooks.infer = (globals, t) => {
	if (t.k === "nat") return { k: "global", name: need_lang_item(globals, "Nat", "a numeral") };
	if (t.k === "str") return { k: "global", name: need_lang_item(globals, "String", "a string literal") };
	return null;
};

