import { test, expect } from "bun:test";
import { parse } from "./parser";
import { expand } from "./expand";
import { check_program, new_globals } from "./check";
import { export_to_lean } from "./lean_export";

test("all defs check", async () => {
	const statements = await expand(
		"./defs/main.txt",
		async (path) => await Bun.file(path).text(),
	);
	const globals = new_globals();
	expect(() => check_program(globals, statements)).not.toThrow();
});

test("pattern matching", async () => {
	const statements = await expand(
		"main.txt",
		async (path) => `
		left : ( A : Type ) -> A -> A -> A;
		left A a b : A := a;
		`,
	);
	const globals = new_globals();
	expect(() => check_program(globals, statements)).not.toThrow();
});

// `P -> P` is a Prop, not a Type, however big P is: a pi lands in the sort of
// its codomain. Nat.rec style case arms depend on this.
test("a pi into Prop is a Prop", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		Nat : Type;
		imp : Nat -> Prop -> Prop := (n : Nat) => (P : Prop) => P -> P;
		`,
	);
	const globals = new_globals();
	expect(() => check_program(globals, statements)).not.toThrow();
});

test("pattern variables are not confused with each other", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		f : ( A : Type ) -> ( B : Type ) -> A -> B;
		f A B a : B := a;
		`,
	);
	const globals = new_globals();
	// `a : A` is not a `B`, even though A and B are both opaque values of Type
	expect(() => check_program(globals, statements)).toThrow();
});

test("parse_directive", () => {
	const source = `
	@require "prop"
	`;

	const result = parse(source);
	expect(result.dependencies).toEqual(["prop"]);
});

// Every `<idx> #KIND ...` line must introduce a fresh index and may only
// mention indices introduced earlier, which is the invariant the Lean export
// format relies on to be readable in a single pass.
function assert_indices_well_formed(text: string) {
	const seen = { N: new Set([0]), U: new Set([0]), E: new Set<number>() };
	const bucket = (k: string) =>
		k.startsWith("N") ? seen.N : k.startsWith("U") ? seen.U : seen.E;
	// which bucket each argument position of each kind refers to
	const refs: Record<string, string[]> = {
		NS: ["N"], NI: ["N"], US: ["U"], UM: ["U", "U"], UIM: ["U", "U"],
		UP: ["N"], ES: ["U"], EV: [], EA: ["E", "E"],
		EL: ["", "N", "E", "E"], EP: ["", "N", "E", "E"],
	};
	for (const line of text.split("\n")) {
		if (!line || line.startsWith("#")) continue;
		const [idx, kind, ...args] = line.split(" ");
		const k = kind!.slice(1);
		const target = bucket(k);
		expect(target.has(+idx!)).toBe(false);
		const spec = k === "EC" ? ["N", ...args.slice(1).map(() => "U")] : refs[k]!;
		expect(spec).toBeDefined();
		spec.forEach((b, i) => {
			if (b === "") return;
			expect(bucket(b).has(+args[i]!)).toBe(true);
		});
		target.add(+idx!);
	}
}

test("exports all defs to the lean export format", async () => {
	const statements = await expand(
		"./defs/main.txt",
		async (path) => await Bun.file(path).text(),
	);
	const result = export_to_lean(statements);
	assert_indices_well_formed(result.text);
	expect(result.axioms + result.definitions).toBe(
		statements.filter((s) => s.pat.type === "ident").length,
	);
	expect(result.text).toContain("#NS 0 Nat");
});

// The JSON format carries the same content, but readers require every
// back-reference to be continuous: names and levels start at 1, since index 0 is
// the anonymous name and the universe zero, and expressions start at 0.
test("exports all defs to the json export format", async () => {
	const statements = await expand(
		"./defs/main.txt",
		async (path) => await Bun.file(path).text(),
	);
	const result = export_to_lean(statements, { format: "json" });
	const lines = result.text.trim().split("\n").map((l) => JSON.parse(l));
	expect(lines[0].meta.format.version).toBe("3.1.0");

	const next: Record<string, number> = { in: 1, il: 1, ie: 0 };
	let declarations = 0;
	for (const line of lines.slice(1)) {
		const key = ["in", "il", "ie"].find((k) => k in line);
		if (key === undefined) {
			// anything without an index of its own is a declaration
			expect("axiom" in line || "def" in line).toBe(true);
			declarations++;
			continue;
		}
		expect(line[key]).toBe(next[key]!++);
	}
	expect(declarations).toBe(result.axioms + result.definitions);
});

test("a single full arity rule exports as a definition", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		left : ( A : Type ) -> A -> A -> A;
		left A a b : A := a;
		`,
	);
	const result = export_to_lean(statements);
	assert_indices_well_formed(result.text);
	expect(result.definitions).toBe(1);
	expect(result.skipped).toEqual([]);
	// fun (A : Sort 1) (a : A) (b : A) => a
	expect(result.text).toContain("#DEF");
	expect(result.text.split("\n").filter((l) => l.includes("#EL")).length).toBe(3);
});

test("real pattern matching stays an axiom", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		Nat : Type;
		Nat.zero : Nat;
		Nat.succ : Nat -> Nat;
		Pred : Nat -> Nat;
		Pred Nat.zero : Nat := Nat.zero;
		Pred (Nat.succ n) : Nat := n;
		`,
	);
	const result = export_to_lean(statements);
	expect(result.definitions).toBe(0);
	expect(result.skipped.map((s) => s.name)).toEqual(["Pred"]);
});

test("SORRY is instantiated at the universe of what it proves", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		Nat : Type;
		Eq : (A : Type) -> A -> A -> Prop;
		prop_level : (x : Nat) -> Eq Nat x x := (x : Nat) => SORRY (Eq Nat x x);
		type_level : Nat := SORRY Nat;
		`,
	);
	const result = export_to_lean(statements);
	assert_indices_well_formed(result.text);
	const lines = result.text.split("\n");
	const sorry = +lines.find((l) => l.endsWith("#NS 0 SORRY"))!.split(" ")[0]!;
	// `EC <SORRY> 0` is Sort 0, ie Prop; `EC <SORRY> 1` is Sort 1, ie Type
	expect(lines.some((l) => l.endsWith(`#EC ${sorry} 0`))).toBe(true);
	expect(lines.some((l) => l.endsWith(`#EC ${sorry} 1`))).toBe(true);
});
