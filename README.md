# awful-proof-assistant
Proof assistant written in typescript with minimal syntax that is just complicated enough to prove basic theorems
Implements dependent type theory (and subtypes/supertypes don't exist)

# Markers
I want to keep the language simple but creating inductive types as (effectively) axioms is kind of unsound. Markers exist to hint the checker and don't change the rules of the language.
`@inductive` - Marks this declaration as an inductive type
`@intro(X)` - Marks this declaration as an introduction rule for the inductive type X.
`@rec(X)` - Marks this declaration as the recursor's type for X based on the introduction rules.
`@iota(X)` - Marks this definition as one of the computation rules for the recursor of X.

# Limitations
- No type inference (this one hurts a lot) Everything must be written out explicitly over and over again, and a single mistake will fuck up the entire proof
- Unhelpful error messages that clog up the entire output
- Probably super unoptimized as well

# todo
Embrace the exponentials :sob:
define multiplication, power, integers, and rationals

To run: `bun run .`, which reports how long each file took to parse and every
declaration that took more than 10ms to check. `bun run . --all` times every
declaration and rule.
