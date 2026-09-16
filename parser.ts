// Tokenizer + recursive-descent parser for the proof language.

export type TokenType =
	| "ident"
	| "("
	| ")"
	| "->"
	| "=>"
	| ":="
	| ":"
	| ";"
	| "comment"
	| "string"
	| "@require"
	| "directive";

export type Token = { type: TokenType; raw: string };

// Char-code range checks instead of a regex .test() per character: a regex
// engine dispatch is far more expensive than a couple of numeric compares,
// and this runs once per character of every identifier in the source.
function is_ident_char(code: number): boolean {
	return (
		(code >= 48 && code <= 57) || // 0-9
		(code >= 65 && code <= 90) || // A-Z
		(code >= 97 && code <= 122) || // a-z
		code === 95 || // _
		code === 46 // .
	);
}

export function lex_all(source: string): Token[] {
	const tokens: Token[] = [];
	let i = 0;
	const n = source.length;
	while (i < n) {
		const c = source[i]!;
		const code = source.charCodeAt(i);
		if (c === " " || c === "\t" || c === "\r" || c === "\n") {
			// consume the whole run at once rather than one char per outer
			// loop iteration
			i++;
			while (i < n) {
				const wc = source[i]!;
				if (wc !== " " && wc !== "\t" && wc !== "\r" && wc !== "\n") break;
				i++;
			}
			continue;
		}
		if (c === "/" && source[i + 1] === "/") {
			const start = i;
			while (i < n && source[i] !== "\n") i++;
			tokens.push({ type: "comment", raw: source.slice(start, i) });
			continue;
		}
		if (c === '"') {
			const start = i;
			i++;
			while (i < n && source[i] !== '"') i++;
			i++; // closing quote (or EOF)
			tokens.push({ type: "string", raw: source.slice(start, i) });
			continue;
		}
		if (c === "@") {
			const start = i;
			i++;
			while (i < n && is_ident_char(source.charCodeAt(i))) i++;
			const raw = source.slice(start, i);
			tokens.push({ type: raw === "@require" ? "@require" : "directive", raw });
			continue;
		}
		if (c === "-" && source[i + 1] === ">") {
			tokens.push({ type: "->", raw: "->" });
			i += 2;
			continue;
		}
		if (c === "=" && source[i + 1] === ">") {
			tokens.push({ type: "=>", raw: "=>" });
			i += 2;
			continue;
		}
		if (c === ":" && source[i + 1] === "=") {
			tokens.push({ type: ":=", raw: ":=" });
			i += 2;
			continue;
		}
		if (c === "(" || c === ")" || c === ":" || c === ";") {
			tokens.push({ type: c, raw: c });
			i += 1;
			continue;
		}
		if (is_ident_char(code)) {
			const start = i;
			i++;
			while (i < n && is_ident_char(source.charCodeAt(i))) i++;
			tokens.push({ type: "ident", raw: source.slice(start, i) });
			continue;
		}
		throw new Error(`unexpected character '${c}' at offset ${i}`);
	}
	return tokens;
}

// ---------------------------------------------------------------------------
// AST
// ---------------------------------------------------------------------------

export type Binding = { type: "binding"; ident: string; ty: Expr };

export type Expr =
	| { type: "ident"; ident: string }
	| { type: "application"; fun: Expr; value: Expr }
	| { type: "lambda"; head: Expr | Binding; tail: Expr }
	| { type: "pi"; head: Expr | Binding; tail: Expr }
	| Binding;

export type Directive = { name: string; arg: string | null };

export type Statement = {
	pat: Expr;
	ty: Expr;
	def: Expr | null;
	directives: Directive[];
};

export type ParseResult = { statements: Statement[]; dependencies: string[] };

// walks application spines to the leftmost head
export function first_ident(expr: Expr): { ident: string } {
	let cur = expr;
	while (cur.type === "application") cur = cur.fun;
	if (cur.type !== "ident") {
		throw new Error(`expected an identifier at the head of ${cur.type}`);
	}
	return cur;
}

// ---------------------------------------------------------------------------
// Parser
// ---------------------------------------------------------------------------

export function parse(source: string): ParseResult {
	const tokens = lex_all(source).filter((t) => t.type !== "comment");
	let pos = 0;

	function peek(): Token | undefined {
		return tokens[pos];
	}
	function at(type: TokenType): boolean {
		return tokens[pos]?.type === type;
	}
	function advance(): Token {
		const t = tokens[pos];
		if (!t) throw new Error("unexpected end of input");
		pos++;
		return t;
	}
	function expect(type: TokenType): Token {
		const t = peek();
		if (!t || t.type !== type) {
			throw new Error(
				`expected '${type}' but found ${t ? `'${t.raw}'` : "end of input"}`,
			);
		}
		return advance();
	}

	// full expression grammar: an optional binder head followed by -> or =>,
	// otherwise a plain application-level expression.
	function parse_expr(): Expr {
		const head = parse_head();
		if (at("->")) {
			advance();
			return { type: "pi", head, tail: parse_expr() };
		}
		if (at("=>")) {
			advance();
			return { type: "lambda", head, tail: parse_expr() };
		}
		if (head.type === "binding") {
			throw new Error("found a binding outside lambda or pi");
		}
		return head;
	}

	// either `(ident : type)`, or a plain application expression standing in
	// as an anonymous binder domain.
	function parse_head(): Expr | Binding {
		if (
			at("(") &&
			tokens[pos + 1]?.type === "ident" &&
			tokens[pos + 2]?.type === ":"
		) {
			advance(); // (
			const ident = advance().raw;
			advance(); // :
			const ty = parse_expr();
			expect(")");
			return { type: "binding", ident, ty };
		}
		return parse_app();
	}

	function parse_app(): Expr {
		let e = parse_atom();
		while (at("ident") || at("(")) {
			const value = parse_atom();
			e = { type: "application", fun: e, value };
		}
		return e;
	}

	function parse_atom(): Expr {
		if (at("ident")) {
			return { type: "ident", ident: advance().raw };
		}
		if (at("(")) {
			advance();
			const e = parse_expr();
			expect(")");
			return e;
		}
		const t = peek();
		throw new Error(
			`expected an expression but found ${t ? `'${t.raw}'` : "end of input"}`,
		);
	}

	function unquote(raw: string): string {
		return raw.startsWith('"') && raw.endsWith('"') ? raw.slice(1, -1) : raw;
	}

	const dependencies: string[] = [];
	const statements: Statement[] = [];

	while (pos < tokens.length) {
		if (at("@require")) {
			advance();
			const str = expect("string");
			dependencies.push(unquote(str.raw));
			if (at(";")) advance();
			continue;
		}

		const directives: Directive[] = [];
		while (at("directive")) {
			const raw = advance().raw;
			const name = raw.slice(1);
			let arg: string | null = null;
			if (at("(")) {
				advance();
				arg = expect("ident").raw;
				expect(")");
			}
			directives.push({ name, arg });
		}

		const pat = parse_app();
		expect(":");
		const ty = parse_expr();
		let def: Expr | null = null;
		if (at(":=")) {
			advance();
			def = parse_expr();
		}
		expect(";");
		statements.push({ pat, ty, def, directives });
	}

	return { statements, dependencies };
}
