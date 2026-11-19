// What @debug shows: a full normal form, printed back as source.
import { type Globals, type Term, abstract_local, apply, fresh_local, instantiate, is_prop_typed, rec_arity, unwind, whnf } from "./kernel";
import { lang_item, unfold_str } from "./native";

// The inverse of unfold_str: a normalized String.nil / String.cons-of-Char.mk
// chain (e.g. what appending two strings leaves behind, one layer of the left
// one at a time) goes back to a native string when it ends in nil or in a
// native string. Null when `t` is not shaped like that.
export function try_fold_str(globals: Globals, t: Term): Term | null {
	const mk = lang_item(globals, "Char.mk");
	if (
		!mk ||
		!lang_item(globals, "String.nil") ||
		!lang_item(globals, "String.cons") ||
		unwind(t).head.k !== "global"
	) {
		return null;
	}
	if (show(t) === show(unfold_str(globals, ""))) return { k: "str", s: "" };
	const sample = unwind(unfold_str(globals, "a"));
	const n = sample.args.length;
	const { head, args } = unwind(t);
	if (head.k !== "global" || head.name !== (sample.head as { name: string }).name) return null;
	if (args.length !== n) return null;
	for (let i = 0; i < n - 2; i++) {
		if (show(args[i]!) !== show(sample.args[i]!)) return null;
	}
	const ch = unwind(args[n - 2]!);
	const code = ch.args[0];
	if (!(ch.head.k === "global" && ch.head.name === mk && code?.k === "nat")) return null;
	const rest = args[n - 1]!;
	if (rest.k !== "str") return null;
	return { k: "str", s: String.fromCodePoint(Number(code.n)) + rest.s };
}

// Full normal form, under binders too: what @debug shows.
export function normalize(globals: Globals, term: Term): Term {
	const w = whnf(globals, term);
	switch (w.k) {
		case "lam":
		case "pi": {
			const dom = normalize(globals, w.dom);
			const l = fresh_local(w.dom);
			const body = normalize(globals, instantiate(w.body, l));
			return { k: w.k, dom, body: abstract_local(body, l) };
		}
		case "app": {
			const { head, args } = unwind(w);
			// a recursor that could not fire (its target is stuck on an axiom
			// or a variable) stays as it is: normalizing its arguments would
			// unfold every definition they mention, for no gain
			const rec = head.k === "global" ? globals.get(head.name)?.rec_info : undefined;
			if (rec && args.length >= rec_arity(rec)) return w;
			// a proof is not worth evaluating (it is irrelevant by definition) and
			// can be enormous, so it is shown as `_`
			const out = apply(
				head,
				args.map((a) =>
					is_prop_typed(globals, a) ? ({ k: "global", name: "_" } as Term) : normalize(globals, a),
				),
			);
			return try_fold_str(globals, out) ?? out;
		}
		default:
			return w;
	}
}

// Readable source-ish text for a normalized term; `names` are the binders
// in scope, innermost last.
export function show(t: Term, names: string[] = [], mk?: string): string {
	switch (t.k) {
		case "sort":
			return t.s === 0 ? "Prop" : t.s === 1 ? "Type" : "Type1";
		case "global":
			return t.name;
		case "local":
			return `?${t.id}`;
		case "bvar":
			return names[names.length - 1 - t.i] ?? `#${t.i}`;
		case "nat":
			return String(t.n);
		case "str":
			return JSON.stringify(t.s);
		case "app": {
			const { head, args } = unwind(t);
			// a character, as written: 'H' rather than the Char.mk and its proof
			if (mk && head.k === "global" && head.name === mk && args[0]?.k === "nat") {
				return `'${String.fromCodePoint(Number(args[0].n))}'`;
			}
			return `(${[head, ...args].map((x) => show(x, names, mk)).join(" ")})`;
		}
		case "lam":
		case "pi": {
			const n = `x${names.length}`;
			const arrow = t.k === "lam" ? "=>" : "->";
			return `((${n} : ${show(t.dom, names, mk)}) ${arrow} ${show(t.body, [...names, n], mk)})`;
		}
	}
}
