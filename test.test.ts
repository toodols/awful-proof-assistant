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
		@inductive
		N : Type;
		@intro(N)
		N.z : N;
		@rec(N)
		N.rec : (motive : N -> Type) -> (case_z : motive N.z) ->
			(target : N) -> motive target;
		@iota(N)
		N.rec motive case_z N.z : motive N.z := case_z;
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
		@axiom
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
		@inductive
		Lst : (A : Type) -> Type;
		@intro(Lst)
		Lst.nil : (A : Type) -> Lst A;
		@rec(Lst)
		Lst.rec : (A : Type) -> (motive : Lst A -> Type) ->
			(case_nil : motive (Lst.nil A)) ->
			(target : Lst A) -> motive target;
		@iota(Lst)
		Lst.rec A motive case_nil (Lst.nil B) : motive (Lst.nil A) := case_nil;
		`,
	);
	const globals = new_globals();
	// the rule is about `Lst B`, which is not the `Lst A` the recursor takes,
	// even though A and B are both opaque values of Type
	expect(() => check_program(globals, statements)).toThrow();
});

// A declaration's type is the one thing nothing else looks at when there is no
// definition, so both halves of every arrow in it have to be checked.
test("a term cannot stand where a type belongs", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@axiom
		Nat : Type;
		@axiom
		Foo : ( A : Type ) -> A -> Prop;
		@axiom
		bad : ( A : Type ) -> Foo A -> Nat;
		`,
	);
	const globals = new_globals();
	// `Foo A` is a predicate, of type `A -> Prop`, not a type
	expect(() => check_program(globals, statements)).toThrow();
});

test("a defined global applied to several arguments unfolds", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@axiom
		Nat : Type;
		@axiom
		Eq : ( A : Type ) -> ( a : A ) -> ( b : A ) -> Prop;
		@axiom
		Eq.refl : ( A : Type ) -> ( x : A ) -> Eq A x x;
		Fixes : ( A : Type ) -> ( f : A -> A ) -> Prop :=
			(A : Type) => (f : A -> A) => (a : A) -> Eq A (f a) (f a);
		id_fixes : Fixes Nat ((n : Nat) => n) := (a : Nat) => Eq.refl Nat a;
		`,
	);
	const globals = new_globals();
	// `Fixes Nat (n => n)` has to unfold and reduce all the way to
	// `(a : Nat) -> Eq Nat a a`, past both of its arguments
	expect(() => check_program(globals, statements)).not.toThrow();
});

// Prop : Type : Type1, and the ladder stops there.
test("Type lives in Type1", async () => {
	const statements = await expand("main.txt", async () => `t : Type1 := Type;`);
	expect(() => check_program(new_globals(), statements)).not.toThrow();
});

test("Type does not live in itself", async () => {
	const statements = await expand("main.txt", async () => `t : Type := Type;`);
	expect(() => check_program(new_globals(), statements)).toThrow();
});

test("a pi is as big as its largest half", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@axiom
		Nat : Type;
		motive_ty : Type1 := Nat -> Type;
		`,
	);
	// `Nat -> Type` is a Type1, not a Type: max(1, 2)
	expect(() => check_program(new_globals(), statements)).not.toThrow();

	const too_small = await expand(
		"main.txt",
		async () => `
		@axiom
		Nat : Type;
		motive_ty : Type := Nat -> Type;
		`,
	);
	expect(() => check_program(new_globals(), too_small)).toThrow();
});

test("Prop stays impredicative", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@axiom
		Nat : Type;
		imp : Nat -> Prop -> Prop := (n : Nat) => (P : Prop) => (A : Type) -> P;
		`,
	);
	// quantifying over Type still lands in Prop, because the codomain does
	expect(() => check_program(new_globals(), statements)).not.toThrow();
});

test("Type1 exports as Sort 2", async () => {
	const statements = await expand("main.txt", async () => `t : Type1 := Type;`);
	const result = export_to_lean(statements, { format: "json" });
	const lines = result.text.trim().split("\n").map((l) => JSON.parse(l));
	// Sort 2 needs two successors of the universe zero at index 0
	expect(lines).toContainEqual({ il: 1, succ: 0 });
	expect(lines).toContainEqual({ il: 2, succ: 1 });
	expect(lines.some((l) => l.sort === 2)).toBe(true);
});

// A declaration with no `:=` is an assumption, and has to say so.
test("an assumption has to say so", async () => {
	const check = async (source: string) => {
		const statements = await expand("main.txt", async () => source);
		return () => check_program(new_globals(), statements);
	};
	expect(await check(`Nat : Type;`)).toThrow();
	expect(await check(`@axiom\nNat : Type;`)).not.toThrow();
	// the marker is a claim about the declaration, so it may not contradict it
	expect(await check(`@axiom\nt : Type := Prop;`)).toThrow();
	// claiming a check that does not exist yet is worse than not claiming it
	expect(await check(`@intro(Nat)\nNat : Type;`)).toThrow();
	expect(await check(`@nonsense\nNat : Type;`)).toThrow();
});

// The web levels are toys, and their premises are assumptions by construction,
// so the UI checks them without requiring the marker.
test("markers can be waived", async () => {
	const statements = await expand("main.txt", async () => `Nat : Type;`);
	expect(() =>
		check_program(new_globals(), statements, { require_markers: false }),
	).not.toThrow();
	// a marker that contradicts its declaration is still wrong either way
	const contradictory = await expand(
		"main.txt",
		async () => `@axiom\nt : Type := Prop;`,
	);
	expect(() =>
		check_program(new_globals(), contradictory, { require_markers: false }),
	).toThrow();
});

// @rec(X) derives the canonical recursor for X and compares, so a written one
// cannot quietly be the wrong shape.
test("a recursor has to be the recursor", async () => {
	const nat = `
		@inductive
		Nat : Type;
		@intro(Nat)
		Nat.zero : Nat;
		@intro(Nat)
		Nat.succ : Nat -> Nat;
	`;
	const check = async (source: string) => {
		const statements = await expand("main.txt", async () => source);
		return () => check_program(new_globals(), statements);
	};
	expect(
		await check(
			nat +
				`
		@rec(Nat)
		Nat.rec :
			(motive : Nat -> Type) ->
			(case_zero : motive Nat.zero) ->
			(case_succ : (n : Nat) -> motive n -> motive (Nat.succ n)) ->
			(target : Nat) ->
			motive target;
		`,
		),
	).not.toThrow();
	// a missing case, and a missing induction hypothesis
	expect(
		await check(
			nat +
				`
		@rec(Nat)
		Nat.rec :
			(motive : Nat -> Type) ->
			(case_succ : (n : Nat) -> motive n -> motive (Nat.succ n)) ->
			(target : Nat) ->
			motive target;
		`,
		),
	).toThrow();
	expect(
		await check(
			nat +
				`
		@rec(Nat)
		Nat.rec :
			(motive : Nat -> Type) ->
			(case_zero : motive Nat.zero) ->
			(case_succ : (n : Nat) -> motive (Nat.succ n)) ->
			(target : Nat) ->
			motive target;
		`,
		),
	).toThrow();
});

// A Prop with more than one constructor may not eliminate into Type: a proof
// could then say which side it came from, and Prop would stop being irrelevant.
test("large elimination is restricted", async () => {
	const or = `
		@inductive
		Or : (a : Prop) -> (b : Prop) -> Prop;
		@intro(Or)
		Or.inl : (a : Prop) -> (b : Prop) -> a -> Or a b;
		@intro(Or)
		Or.inr : (a : Prop) -> (b : Prop) -> b -> Or a b;
	`;
	const rec = (sort: string) => `
		@rec(Or)
		Or.rec :
			(a : Prop) -> (b : Prop) ->
			(motive : Or a b -> ${sort}) ->
			(case_inl : (x : a) -> motive (Or.inl a b x)) ->
			(case_inr : (y : b) -> motive (Or.inr a b y)) ->
			(target : Or a b) ->
			motive target;
	`;
	const check = async (source: string) => {
		const statements = await expand("main.txt", async () => source);
		return () => check_program(new_globals(), statements);
	};
	expect(await check(or + rec("Prop"))).not.toThrow();
	expect(await check(or + rec("Type"))).toThrow();
});

// The point of the markers: the trust base is greppable, and it matches what
// the exporter reports. @inductive and @intro still export as axioms, since
// nothing generates recursors yet, so every marked declaration is one exported
// axiom - the @iota rules mark rules of those declarations, not new ones. A
// proof using SORRY would add an axiom with no declaration of its own to mark,
// which is the one hole in this.
test("every axiom in the export is marked in the source", async () => {
	const statements = await expand(
		"./defs/main.txt",
		async (path) => await Bun.file(path).text(),
	);
	const result = export_to_lean(statements);
	// an @iota rule marks a rule of a declaration that is already counted
	const marked = statements.filter(
		(s) => s.directives.length > 0 && s.pat.type === "ident",
	);
	expect(marked.length).toBe(result.axioms);

	// of those, the ones still taken purely on trust
	const assumed = marked.filter((s) =>
		s.directives.some((d) => d.name === "axiom"),
	);
	expect(assumed.length).toBeLessThan(marked.length);
});

// Nothing here terminates, so the only thing standing between the language and
// `bad : False := bad` is that a name is not in scope until its declaration is
// finished. It has to stay that way.
test("a declaration cannot assume itself", async () => {
	const check = async (source: string) => {
		const statements = await expand("main.txt", async () => source);
		return () => check_program(new_globals(), statements);
	};
	const FALSE = `@inductive\nFalse : Prop;\n`;
	expect(await check(FALSE + `bad : False := bad;`)).toThrow();
	expect(
		await check(FALSE + `bad1 : False := bad2;\nbad2 : False := bad1;`),
	).toThrow();
	// the type may not refer to itself either
	expect(await check(`T : Type := T;`)).toThrow();
});

// Iota: a recursor applied to a constructor reduces to the matching case, so
// arithmetic computes and its equations hold by reflexivity. The exporter still
// emits inductives as axioms, so these proofs cannot be exported yet - the defs
// keep the equations as assumptions until it can.
test("recursors compute", async () => {
	const nat = `
		@inductive
		Nat : Type;
		@intro(Nat)
		Nat.zero : Nat;
		@intro(Nat)
		Nat.succ : Nat -> Nat;
		@rec(Nat)
		Nat.rec :
			(motive : Nat -> Type) ->
			(case_zero : motive Nat.zero) ->
			(case_succ : (n : Nat) -> motive n -> motive (Nat.succ n)) ->
			(target : Nat) ->
			motive target;
		@iota(Nat)
		Nat.rec motive case_zero case_succ Nat.zero :
			motive Nat.zero := case_zero;
		@iota(Nat)
		Nat.rec motive case_zero case_succ (Nat.succ n) :
			motive (Nat.succ n) :=
			case_succ n (Nat.rec motive case_zero case_succ n);
		@axiom
		Eq : ( A : Type ) -> ( a : A ) -> ( b : A ) -> Prop;
		@axiom
		Eq.refl : ( A : Type ) -> ( x : A ) -> Eq A x x;
		Nat.Add : Nat -> Nat -> Nat := (a : Nat) => (b : Nat) =>
			Nat.rec ((n : Nat) => Nat) a ((n : Nat) => (ih : Nat) => Nat.succ ih) b;
	`;
	const check = async (extra: string) => {
		const statements = await expand("main.txt", async () => nat + extra);
		return () => check_program(new_globals(), statements);
	};

	// x + 0 = x, by reflexivity rather than by assumption
	expect(
		await check(`
		add_zero : (x : Nat) -> Eq Nat (Nat.Add x Nat.zero) x :=
			(x : Nat) => Eq.refl Nat x;
		`),
	).not.toThrow();

	// and concrete arithmetic, which needs the recursor to fire twice
	expect(
		await check(`
		two : Nat := Nat.succ (Nat.succ Nat.zero);
		four : Nat := Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)));
		sum : Eq Nat (Nat.Add two two) four := Eq.refl Nat four;
		`),
	).not.toThrow();

	// it is reduction, not wishful thinking
	expect(
		await check(`
		two : Nat := Nat.succ (Nat.succ Nat.zero);
		three : Nat := Nat.succ (Nat.succ (Nat.succ Nat.zero));
		sum : Eq Nat (Nat.Add two two) three := Eq.refl Nat three;
		`),
	).toThrow();
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
	let blocks = 0;
	for (const line of lines.slice(1)) {
		const key = ["in", "il", "ie"].find((k) => k in line);
		if (key === undefined) {
			// anything without an index of its own is a declaration, and an
			// inductive is one line carrying several
			if ("inductive" in line) {
				const ind = line.inductive;
				blocks +=
					ind.types.length + ind.ctors.length + ind.recs.length;
				continue;
			}
			expect("axiom" in line || "def" in line).toBe(true);
			declarations++;
			continue;
		}
		expect(line[key]).toBe(next[key]!++);
	}
	expect(declarations).toBe(result.axioms + result.definitions);
	expect(blocks).toBe(result.inductives);
	// Nat really is an inductive in the JSON, not an axiom
	expect(blocks).toBeGreaterThan(0);
});

// An inductive carries its constructors and a universe polymorphic recursor, so
// the kernel can reduce it - which is what lets arithmetic be proved by
// reflexivity and survive the export.
test("an inductive exports with a polymorphic recursor", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@inductive
		Nat : Type;
		@intro(Nat)
		Nat.zero : Nat;
		@intro(Nat)
		Nat.succ : Nat -> Nat;
		@rec(Nat)
		Nat.rec :
			(motive : Nat -> Type) ->
			(case_zero : motive Nat.zero) ->
			(case_succ : (n : Nat) -> motive n -> motive (Nat.succ n)) ->
			(target : Nat) ->
			motive target;
		`,
	);
	const result = export_to_lean(statements, { format: "json" });
	// the type, both constructors and the recursor, all in one block
	expect(result.inductives).toBe(4);
	expect(result.axioms).toBe(0);

	const lines = result.text.trim().split("\n").map((l) => JSON.parse(l));
	const block = lines.find((l) => "inductive" in l)!.inductive;
	expect(block.types[0].numParams).toBe(0);
	expect(block.ctors.map((c: { numFields: number }) => c.numFields)).toEqual([0, 1]);
	// one level parameter, and one reduction rule per constructor
	expect(block.recs[0].levelParams.length).toBe(1);
	expect(block.recs[0].rules.length).toBe(2);
	expect(block.recs[0].k).toBe(false);

	// the text format has no inductives and keeps emitting axioms
	const text = export_to_lean(statements, { format: "text" });
	expect(text.inductives).toBe(0);
	expect(text.axioms).toBe(4);
});

test("a single full arity rule exports as a definition", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@axiom
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
		@axiom
		Nat : Type;
		@axiom
		Nat.zero : Nat;
		@axiom
		Nat.succ : Nat -> Nat;
		@axiom
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
		@axiom
		Nat : Type;
		@axiom
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

// ---------------------------------------------------------------------------
// @iota
//
// A recursor's iota rules are what it does on each constructor, and nothing
// else may have them: every other definition is written in terms of a recursor.
// ---------------------------------------------------------------------------

// every iota test needs a type to eliminate
const NAT = `
	@inductive
	Eq : (A : Type) -> A -> A -> Prop;
	@intro(Eq)
	Eq.refl : (A : Type) -> (x : A) -> Eq A x x;
	@inductive
	N : Type;
	@intro(N)
	N.z : N;
	@intro(N)
	N.s : N -> N;
`;

const NREC = `
	@rec(N)
	N.rec : (motive : N -> Type) -> (case_z : motive N.z) ->
		(case_s : (n : N) -> motive n -> motive (N.s n)) ->
		(target : N) -> motive target;
`;

const checks = async (src: string) => {
	const statements = await expand("main.txt", async () => NAT + src);
	return () => check_program(new_globals(), statements);
};

test("a recursor reduces by its iota rules", async () => {
	expect(
		await checks(
			NREC +
				`
		@iota(N)
		N.rec motive case_z case_s N.z : motive N.z := case_z;
		@iota(N)
		N.rec motive case_z case_s (N.s n) : motive (N.s n) :=
			case_s n (N.rec motive case_z case_s n);

		N.double : N -> N := (n : N) =>
			N.rec ((t : N) => N) N.z ((m : N) => (ih : N) => N.s (N.s ih)) n;
		// only reduction can close this
		four : Eq N (N.double (N.s (N.s N.z))) (N.s (N.s (N.s (N.s N.z)))) :=
			Eq.refl N (N.s (N.s (N.s (N.s N.z))));
		`,
		),
	).not.toThrow();
});

test("an iota rule may name a parameter twice over", async () => {
	expect(
		await checks(`
		@inductive
		Lst : (A : Type) -> Type;
		@intro(Lst)
		Lst.nil : (A : Type) -> Lst A;
		@intro(Lst)
		Lst.cons : (A : Type) -> A -> Lst A -> Lst A;
		@rec(Lst)
		Lst.rec : (A : Type) -> (motive : Lst A -> Type) ->
			(case_nil : motive (Lst.nil A)) ->
			(case_cons : (x : A) -> (xs : Lst A) -> motive xs ->
				motive (Lst.cons A x xs)) ->
			(target : Lst A) -> motive target;
		@iota(Lst)
		Lst.rec A motive case_nil case_cons (Lst.nil A) :
			motive (Lst.nil A) := case_nil;
		@iota(Lst)
		Lst.rec A motive case_nil case_cons (Lst.cons A x xs) :
			motive (Lst.cons A x xs) :=
			case_cons x xs (Lst.rec A motive case_nil case_cons xs);

		Lst.len : (A : Type) -> Lst A -> N := (A : Type) => (l : Lst A) =>
			Lst.rec A ((t : Lst A) => N) N.z
				((x : A) => (xs : Lst A) => (ih : N) => N.s ih) l;
		two : Eq N (Lst.len N (Lst.cons N N.z (Lst.cons N N.z (Lst.nil N))))
			(N.s (N.s N.z)) := Eq.refl N (N.s (N.s N.z));
		`),
	).not.toThrow();
});

// A recursor with no iota rules at all is the old arrangement, where reduction
// knows what a recursor does. One given some of them has to be given the rest.
test("a recursor may have no iota rules", async () => {
	expect(await checks(NREC)).not.toThrow();
});

test("iota rules have to cover every constructor", async () => {
	expect(
		await checks(
			NREC +
				`
		@iota(N)
		N.rec motive case_z case_s N.z : motive N.z := case_z;
		`,
		),
	).toThrow(/no rule for every constructor/);
});

test("two iota rules may not match the same constructor", async () => {
	expect(
		await checks(
			NREC +
				`
		@iota(N)
		N.rec motive case_z case_s N.z : motive N.z := case_z;
		@iota(N)
		N.rec motive case_z case_s (N.s n) : motive (N.s n) :=
			case_s n (N.rec motive case_z case_s n);
		@iota(N)
		N.rec motive case_z case_s (N.s n) : motive (N.s n) :=
			case_s n (N.rec motive case_z case_s n);
		`,
		),
	).toThrow(/2 rules match N.s/);
});

// The recursor already fixed what it gives at a pattern. A rule that got to
// claim some other type would reduce to a term of the wrong one.
test("an iota rule may not claim a type of its own", async () => {
	expect(
		await checks(
			NREC +
				`
		@iota(N)
		N.rec motive case_z case_s N.z : Prop := N;
		`,
		),
	).toThrow(/the rule claims Prop/);
});

// An indexed family's recursor has to match its index alongside its target,
// which is two patterns at once and not supported yet. Its recursor is also one
// reduction cannot fire on its own, so such a type has no iota at all today.
test("an indexed recursor cannot state its iota rules yet", async () => {
	expect(
		await checks(`
		@inductive
		D : N -> Type;
		@intro(D)
		D.z : D N.z;
		@intro(D)
		D.s : (n : N) -> D n -> D (N.s n);
		@rec(D)
		D.rec : (motive : (n : N) -> D n -> Type) ->
			(case_z : motive N.z D.z) ->
			(case_s : (n : N) -> (d : D n) -> motive n d ->
				motive (N.s n) (D.s n d)) ->
			(n : N) -> (target : D n) -> motive n target;
		@iota(D)
		D.rec motive case_z case_s N.z D.z : motive N.z D.z := case_z;
		`),
	).toThrow(/match on 2 arguments at once/);
});

// A proof of Or must not be able to say which side it came from, which @rec
// catches before there are any rules to write
test("a Prop with two constructors has no recursor into Type", async () => {
	expect(
		await checks(`
		@inductive
		Or : Prop -> Prop -> Prop;
		@intro(Or)
		Or.inl : (a : Prop) -> (b : Prop) -> a -> Or a b;
		@intro(Or)
		Or.inr : (a : Prop) -> (b : Prop) -> b -> Or a b;
		@rec(Or)
		Or.rec : (a : Prop) -> (b : Prop) -> (motive : Or a b -> Type) ->
			(case_inl : (x : a) -> motive (Or.inl a b x)) ->
			(case_inr : (y : b) -> motive (Or.inr a b y)) ->
			(target : Or a b) -> motive target;
		`),
	).toThrow(/may only eliminate into Prop/);
});

// @iota marks a rule, never a declaration
test("a declaration may not be marked @iota", async () => {
	expect(
		await checks(`
		@iota
		f : N -> N;
		`),
	).toThrow(/@iota marks a rule/);
});

// iota is how an eliminator reduces, so the rules belong to one: every other
// definition is written out in terms of a recursor
test("only a recursor has iota rules", async () => {
	expect(
		await checks(`
		@axiom
		f : N -> N;
		@iota(N)
		f N.z : N := N.z;
		`),
	).toThrow(/'f' is not the recursor for N/);
});

// A rule names the type it matches on, the way @intro(Nat) names the type it
// builds
test("an iota rule has to name the type it matches on", async () => {
	expect(
		await checks(
			NREC +
				`
		@iota
		N.rec motive case_z case_s N.z : motive N.z := case_z;
		`,
		),
	).toThrow(/@iota needs the type the rule matches on/);
});

test("an iota rule may not name a type it does not match on", async () => {
	expect(
		await checks(`
		@inductive
		Lst : (A : Type) -> Type;
		@intro(Lst)
		Lst.nil : (A : Type) -> Lst A;
		@rec(N)
		N.rec : (motive : N -> Type) -> (case_z : motive N.z) ->
			(case_s : (n : N) -> motive n -> motive (N.s n)) ->
			(target : N) -> motive target;
		@iota(Lst)
		N.rec motive case_z case_s N.z : motive N.z := case_z;
		`),
	).toThrow(/is not the recursor for Lst/);
});

test("a rule cannot match a constructor of another type", async () => {
	expect(
		await checks(`
		@inductive
		M : Type;
		@intro(M)
		M.t : M;
		@rec(M)
		M.rec : (motive : M -> Type) -> (case_t : motive M.t) ->
			(target : M) -> motive target;
		@iota(M)
		M.rec motive case_t N.z : motive M.t := case_t;
		`),
		// the pattern is typed against the recursor, which is what catches it
	).toThrow(/expected type N to be a subtype of M/);
});

test("a declaration gets exactly one marker", async () => {
	expect(
		await checks(`
		@axiom
		@iota
		f : N -> N;
		`),
	).toThrow(/but a declaration gets exactly one marker/);
});

// ---------------------------------------------------------------------------
// Strict positivity
//
// @inductive is a claim the checker verifies, not an assumption: without
// this, marking any old shape @inductive would be as unchecked as @axiom,
// just without saying so.
// ---------------------------------------------------------------------------

test("a constructor may not put the type to the left of an arrow", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@inductive
		Bad : Type;
		@intro(Bad)
		Bad.intro : (Bad -> Bad) -> Bad;
		`,
	);
	// (Bad -> Bad) -> Bad is Curry's paradox in disguise: Bad.intro applied to
	// itself, by a Y-combinator style fixed point, proves anything at all
	expect(() => check_program(new_globals(), statements)).toThrow(
		/not strictly positive/,
	);
});

test("a directly self-recursive constructor is still fine", async () => {
	const statements = await expand(
		"main.txt",
		async () => `
		@inductive
		N : Type;
		@intro(N)
		N.z : N;
		@intro(N)
		N.s : N -> N;
		`,
	);
	expect(() => check_program(new_globals(), statements)).not.toThrow();
});

// ---------------------------------------------------------------------------
// @lang(Nat)
//
// A Peano-shaped inductive marked @lang(Nat) gets a native bigint behind it:
// numerals type-check as that type, defeq to the constructor chain they
// abbreviate, and a recursor fires on a numeral exactly as it would on a
// chain of Nat.succ.
// ---------------------------------------------------------------------------

const LANG_NAT = `
	@inductive
	@lang(Nat)
	Nat : Type;
	@intro(Nat)
	Nat.zero : Nat;
	@intro(Nat)
	Nat.succ : Nat -> Nat;
	@rec(Nat)
	Nat.rec :
		(motive : Nat -> Type) ->
		(case_zero : motive Nat.zero) ->
		(case_succ : (n : Nat) -> motive n -> motive (Nat.succ n)) ->
		(target : Nat) ->
		motive target;
	@iota(Nat)
	Nat.rec motive case_zero case_succ Nat.zero : motive Nat.zero := case_zero;
	@iota(Nat)
	Nat.rec motive case_zero case_succ (Nat.succ n) : motive (Nat.succ n) :=
		case_succ n (Nat.rec motive case_zero case_succ n);
	@axiom
	Eq : (A : Type) -> A -> A -> Prop;
	@axiom
	Eq.refl : (A : Type) -> (x : A) -> Eq A x x;
	Nat.Add : Nat -> Nat -> Nat := (a : Nat) => (b : Nat) =>
		Nat.rec ((n : Nat) => Nat) a ((n : Nat) => (ih : Nat) => Nat.succ ih) b;
`;

test("a @lang(Nat) numeral defeqs the constructor chain it abbreviates", async () => {
	const statements = await expand(
		"main.txt",
		async () =>
			LANG_NAT +
			`
			three_lit : Nat := 3;
			three_chain : Nat := Nat.succ (Nat.succ (Nat.succ Nat.zero));
			same : Eq Nat three_lit three_chain := Eq.refl Nat three_lit;
			`,
	);
	expect(() => check_program(new_globals(), statements)).not.toThrow();
});

test("a recursor fires on a @lang(Nat) numeral", async () => {
	const statements = await expand(
		"main.txt",
		async () =>
			LANG_NAT +
			`
			sum : Eq Nat (Nat.Add 2 3) 5 := Eq.refl Nat 5;
			`,
	);
	expect(() => check_program(new_globals(), statements)).not.toThrow();
});

test("a wrong @lang(Nat) numeral is still caught", async () => {
	const statements = await expand(
		"main.txt",
		async () =>
			LANG_NAT +
			`
			bad : Eq Nat 2 3 := Eq.refl Nat 2;
			`,
	);
	expect(() => check_program(new_globals(), statements)).toThrow();
});

test("@lang only marks an @inductive declaration, and only Nat", async () => {
	const check = async (source: string) => {
		const statements = await expand("main.txt", async () => source);
		return () => check_program(new_globals(), statements);
	};
	expect(
		await check(`@axiom\n@lang(Nat)\nNat : Type;`),
	).toThrow(/@lang\(Nat\) may only mark an @inductive declaration/);
	expect(
		await check(`@inductive\n@lang(Str)\nS : Type;`),
	).toThrow(/@lang only supports Nat/);
});
