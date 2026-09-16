// TODO: implement the parser from scratch.
//
// This file used to contain a tokenizer + parser for the proof language and
// exported (at least) the following surface, which the rest of the codebase
// still imports:
//
//   export type Token = ...
//   export type Expr =
//     | { type: "global"; ident: string; tokens: Token[] }
//     | { type: "ref"; index: number; tokens: Token[] }          // de Bruijn bound variable
//     | { type: "def"; index: number; tokens: Token[] }          // unresolved pattern variable, pre name-resolution
//     | { type: "application"; fun: Expr; value: Expr; tokens: Token[] }
//     | { type: "lambda"; head: Expr | Binding; tail: Expr; tokens: Token[] }
//     | { type: "pi"; head: Expr | Binding; tail: Expr; tokens: Token[] }
//     | { type: "ident"; ident: string; tokens: Token[] }        // pre name-resolution identifier
//     | { type: "binding"; ident: string; ty: Expr; tokens: Token[] }
//     | { type: "any"; tokens: Token[] }
//     | { type: "sorry"; tokens: Token[] }
//     | { type: "error"; tokens: Token[] }
//     | { type: "value_with_type"; id: number; ty: Expr; tokens: Token[] }; // introduced by the checker, not the parser
//
//   export type Statement = {
//     pat: Expr;          // an ident for a plain declaration, or an application for a pattern-match rule
//     ty: Expr;
//     def: Expr | null;
//     directives: { name: string; arg: string | null }[]; // @axiom / @inductive / @intro(X) / @rec(X) / @iota(X)
//   };
//
//   export function parse(source: string): Statement[]
//   export function first_ident(expr: Expr): { ident: string } // walks application spines to the leftmost head
//
// Callers to satisfy: check.ts, expand.ts, index.ts, lean_export.ts, test.test.ts.
// Look at git history (pre-rewrite) for the previous implementation and design notes.
export {};
