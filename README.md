# awful-proof-assistant
Proof assistant written in typescript with minimal syntax that is just complicated enough to prove basic theorems
Implements dependent type theory (and subtypes/supertypes don't exist)

# Limitations
- ~~ No pattern matching, so Nat.rec, Eq.symm, Eq.trans, Eq.congr, ... must be expressed as axioms ~~
- Still no pattern matching but syntax is semi supported by the checker now
- Proof irrelevance (don't expand Prop) not supported by checker (yet)
- No type inference (this one hurts a lot) Everything must be written out explicitly over and over again, and a single mistake will fuck up the entire proof
- Unhelpful error messages that clog up the entire output
- Probably super unoptimized as well

# todo
define multiplication, power, integers, and rationals

To run: `bun run .`

# Exporting to Lean
`lean_export.ts` translates the defs into the [Lean 4 export format](https://github.com/leanprover/lean4export),
so an external kernel can re-check the proofs. Both spellings of the format are
supported: the flat text one that `trepplein` reads, and the line delimited JSON
one (version 3.1.x) that `nanoda` reads.

```
bun run export                       # defs/main.txt to stdout, text format
bun run export defs/peano.txt -o peano.export
bun run export --check               # typecheck before exporting
bun run export -o main.json          # a .json path switches to the JSON format
bun run export --format json         # or ask for it outright
```

All 61 declarations currently pass `nanoda`. Point it at a config naming the
export file; every declaration here is an axiom or a plain definition, so all
axioms have to be permitted:

```json
{
	"export_file_path": "main.json",
	"unsafe_permit_all_axioms": true,
	"unpermitted_axiom_hard_error": false,
	"print_success_message": true
}
```

`Prop` becomes `Sort 0` and `Type` becomes `Sort 1`. Since this language has no
universe hierarchy, anything that actually relies on `Type : Type` will be
rejected downstream. Declarations without a `:=` export as `#AX`, declarations
with one export as `#DEF`. A pattern rule exports as a definition only when
there is exactly one rule and its arguments are all distinct fresh variables;
real pattern matching has no counterpart in the format, so those names stay
axioms and are reported on stderr.
