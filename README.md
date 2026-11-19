# awful-proof-assistant
Proof assistant written in typescript with minimal syntax that is just complicated enough to prove basic theorems
Implements dependent type theory

# Markers
I want to keep the language simple but creating inductive types as (effectively) axioms is kind of unsound. Markers exist to hint the checker and don't change the rules of the language.
`@inductive` - Marks this declaration as an inductive type
`@intro(X)` - Marks this declaration as an introduction rule for the inductive type X.
`@rec(X)` - Marks this declaration as the recursor's type for X based on the introduction rules.
`@iota(X)` - Marks this definition as one of the computation rules for the recursor of X.
`@debug` - Computes and prints out the definition
`@lang(X)` - Speeds up common definitions with efficient representation, String and Nat

# Limitations
- No type inference (this one hurts a lot) Everything must be written out explicitly over and over again, and a single mistake will fuck up the entire proof
- Unhelpful error messages that clog up the entire output
- Probably super unoptimized as well

# todo
Embrace the exponentials :sob:

To run: `bun run .`, which reports how long each file took to parse and how
long every declaration and rule took to check.
