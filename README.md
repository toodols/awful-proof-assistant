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