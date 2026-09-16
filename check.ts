// TODO: implement the type checker from scratch.
//
// This file used to contain a dependently-typed checker (universes Prop/Type/
// Type1, pi/lambda, beta reduction, opaque values for binders, inductive
// types with @inductive/@intro(X)/@rec(X), and pattern-match declarations
// whose rules are validated as recursor iota rules via @iota(X)) and exported
// the following surface, which the rest of the codebase still imports:
//
//   export function new_globals(): Globals
//   export function print_expr(expr: Expr): string
//   export function check_stmt(globals: Globals, stmt: Statement, opts?: CheckOptions): void
//   export function check_program(globals: Globals, stmts: Statement[], opts?: CheckOptions): void
//   export type CheckOptions = {
//     require_markers?: boolean;
//     on_checked?: (stmt: Statement, ms: number) => void;
//   };
//
// `Globals` is a map from declared name to its type, optional definition,
// pattern-match rules, and (for inductives) its constructors - see git
// history (pre-rewrite) for the previous shape and the extensive design
// comments explaining strict positivity, proof irrelevance, and the
// recursor-derivation approach, before reinventing it.
//
// Callers to satisfy: index.ts, lean_export.ts, test.test.ts.
export {};
