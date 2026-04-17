export type Expr =
	| {
			type: "pi";
			head: Expr;
			tail: Expr;
			tokens: Token[];
	  }
	| {
			type: "lambda";
			head: Expr;
			tail: Expr;
			tokens: Token[];
	  }
	| {
			type: "application";
			fun: Expr;
			value: Expr;
			tokens: Token[];
	  }
	| {
			type: "ident";
			ident: string;
			tokens: Token[];
	  }
	| {
			type: "error";
			tokens: Token[];
	  }
	| {
			type: "any";
			tokens: Token[];
	  }
	| {
			type: "sorry";
			tokens: Token[];
	  }
	| {
			type: "ref";
			index: number;
			tokens: Token[];
	  }
	| {
			type: "binding";
			ident: string;
			ty: Expr;
			tokens: Token[];
	  }
	| {
			type: "def";
			index: number;
			tokens: Token[];
	  }
	| {
			type: "global";
			ident: string;
			tokens: Token[];
	  }
	| {
			type: "value_with_type";
			ty: Expr;
			tokens: Token[];
	  };

export type Statement = {
	type: "statement";
	pat: Expr;
	ty: Expr;
	def: Expr | null;
};

export type Program = {
	statements: Statement[];
	dependencies: string[];
};

export type Token =
	| { type: "ident"; ident: string; start: number; end: number; raw: string }
	| {
			type: "=>" | "->" | ":=" | "(" | ")" | ":" | ";";
			start: number;
			end: number;
			raw: string;
	  }
	| { type: "@require"; start: number; end: number; raw: string }
	| { type: "string"; start: number; end: number; raw: string; value: string }
	| { type: "whitespace"; start: number; end: number; raw: string }
	| {
			type: "comment";
			comment: string;
			start: number;
			end: number;
			raw: string;
	  };

export function lex(text: string, start: number): [Token, number] {
	const ident_regex = /[A-Za-z0-9\._]+/y;
	ident_regex.lastIndex = start;
	let ident = ident_regex.exec(text);
	if (ident) {
		const end = start + ident[0].length;
		return [
			{ type: "ident", ident: ident[0], start, end, raw: ident[0] },
			end,
		];
	}
	const ws_regex = /[\t\r\n ]+/y;
	ws_regex.lastIndex = start;
	let ws = ws_regex.exec(text);
	if (ws) {
		const end = start + ws[0].length;
		return [{ type: "whitespace", start, end, raw: ws[0] }, end];
	}

	const string_regex = /"([^"\\]|\\.)*"/y;
	string_regex.lastIndex = start;
	let string_match = string_regex.exec(text);
	if (string_match) {
		const end = start + string_match[0].length;
		return [
			{
				type: "string",
				value: JSON.parse(string_match[0]),
				start,
				end,
				raw: string_match[0],
			},
			end,
		];
	}

	const line_cmt_regex = /\/\/[^\n]*/y;
	line_cmt_regex.lastIndex = start;
	let line_cmt = line_cmt_regex.exec(text);
	if (line_cmt) {
		const end = start + line_cmt[0].length;
		return [
			{
				type: "comment",
				comment: line_cmt[0],
				start,
				end,
				raw: line_cmt[0],
			},
			end,
		];
	}

	const block_cmt_regex = /\/\*([^\*]|\*[^\/])*\*\//y;
	block_cmt_regex.lastIndex = start;
	let block_cmt = block_cmt_regex.exec(text);
	if (block_cmt) {
		const end = start + block_cmt[0].length;
		return [
			{
				type: "comment",
				comment: block_cmt[0],
				start,
				end,
				raw: block_cmt[0],
			},
			end,
		];
	}

	const directive_regex = /@require\b/y;
	directive_regex.lastIndex = start;
	let directive = directive_regex.exec(text);
	if (directive) {
		const end = start + directive[0].length;
		return [
			{
				type: "@require",
				start,
				end,
				raw: directive[0],
			},
			end,
		];
	}

	const ops = ["=>", "->", ":=", "(", ")", ":", ";"] as const;
	for (const op of ops) {
		if (text.startsWith(op, start)) {
			const end = start + op.length;
			return [
				{
					type: op,
					start,
					end,
					raw: op,
				},
				end,
			];
		}
	}
	throw new Error(
		"lexer consumed no input or invalid match at: " + text.slice(start),
	);
}

type TokenStream = {
	tokens: Token[];
	cursor: number;
};

export function expect_token<T extends Token["type"]>(
	tokens: TokenStream,
	type: T,
) {
	let token;
	while (true) {
		token = tokens.tokens[tokens.cursor];
		if (!token) {
			console.log(
				tokens.tokens
					.slice(tokens.cursor - 5, tokens.cursor + 5)
					.map((t) => t.raw)
					.join(""),
			);
			throw new Error(`expected ${type} but got EOF`);
		}
		if (token.type === "whitespace" || token.type === "comment") {
			tokens.cursor += 1;
			continue;
		}
		if (token.type !== type) {
			console.log(
				tokens.tokens
					.slice(tokens.cursor - 5, tokens.cursor + 5)
					.map((t) => t.raw)
					.join(""),
			);
			throw new Error(`expected ${type} but got ${token.type}`);
		}
		break;
	}
	tokens.cursor += 1;
	return token as Token & { type: T };
}

export function next_token(tokens: TokenStream) {
	while (true) {
		const token = tokens.tokens[tokens.cursor];
		if (!token) {
			return token;
		}
		if (token.type === "whitespace" || token.type === "comment") {
			tokens.cursor += 1;
			continue;
		}
		tokens.cursor += 1;
		return token;
	}
}

export function peek_token(tokens: TokenStream, ahead = 0) {
	let tempCursor = tokens.cursor;
	let count = 0;
	while (true) {
		const token = tokens.tokens[tempCursor];
		if (!token) {
			return token;
		}
		if (token.type === "whitespace" || token.type === "comment") {
			tempCursor += 1;
			continue;
		}
		if (count === ahead) {
			return token;
		}
		count += 1;
		tempCursor += 1;
	}
}

export function parse_atom(tokens: TokenStream): Expr {
	if (peek_token(tokens)?.type === "(") {
		const collectedTokens: Token[] = [];
		collectedTokens.push(expect_token(tokens, "("));
		let res;
		// if the next two tokens are ident and :, treat this as a named binding
		// else it is just a regular expression inside parentheses
		const first = peek_token(tokens);
		const second = peek_token(tokens, 1);
		if (first?.type === "ident" && second?.type === ":") {
			collectedTokens.push(expect_token(tokens, "ident"));
			collectedTokens.push(expect_token(tokens, ":"));
			const expr = parse_expression(tokens);
			collectedTokens.push(...expr.tokens);
			res = {
				type: "binding",
				ident: (collectedTokens[1]! as Token & { type: "ident" }).ident,
				ty: expr,
				tokens: collectedTokens,
			} as const;
		} else {
			const expr = parse_expression(tokens);
			collectedTokens.push(...expr.tokens);
			res = { ...expr, tokens: collectedTokens };
		}
		collectedTokens.push(expect_token(tokens, ")"));
		return { ...res, tokens: collectedTokens };
	} else if (peek_token(tokens)?.type === "ident") {
		const ident = expect_token(tokens, "ident");
		return { type: "ident", ident: ident.ident, tokens: [ident] };
	}
	throw new Error("not an atom");
}

// a -> b -> c = a -> (b -> c)
// a -> b => c
// -> is right associative
// a b c = (a b) c
// application  is left associative
// application has higher precedence than application
export function parse_expression(tokens: TokenStream): Expr {
	const collectedTokens: Token[] = [];
	const tail: Expr[] = [];
	const ops = [];
	const expr = parse_atom(tokens);
	collectedTokens.push(...expr.tokens);
	while (true) {
		// if the next token is an ident or (, op is application and parse an atom
		if (
			peek_token(tokens)?.type === "ident" ||
			peek_token(tokens)?.type === "("
		) {
			tail.push(parse_atom(tokens));
			collectedTokens.push(...tail[tail.length - 1]!.tokens);
			ops.push("application");
		}
		// if the next token is a =>, op is lambda and parse an atom
		else if (peek_token(tokens)?.type === "=>") {
			collectedTokens.push(expect_token(tokens, "=>"));
			tail.push(parse_atom(tokens));
			collectedTokens.push(...tail[tail.length - 1]!.tokens);
			ops.push("lambda");
		}
		// if the next token is a ->, op is pi and parse an atom
		else if (peek_token(tokens)?.type === "->") {
			collectedTokens.push(expect_token(tokens, "->"));
			tail.push(parse_atom(tokens));
			collectedTokens.push(...tail[tail.length - 1]!.tokens);
			ops.push("pi");
		} else {
			break;
		}
	}

	const cur_expr: Expr[] = [expr];
	const r_assoc_ops: ("lambda" | "pi")[] = [];

	for (let i = 0; i < ops.length; i++) {
		if (ops[i] === "application") {
			let left = cur_expr.pop()!;
			let right = tail[i]!;
			cur_expr.push({
				type: "application",
				fun: left,
				value: right,
				tokens: [...left.tokens, ...right.tokens], // for application, tokens are combined
			});
		} else {
			r_assoc_ops.push(ops[i] as "lambda" | "pi");
			cur_expr.push(tail[i]!);
		}
	}

	let result = cur_expr.pop()!;
	while (r_assoc_ops.length > 0) {
		let op = r_assoc_ops.pop()!;
		let head = cur_expr.pop()!;

		result = {
			type: op,
			head: head,
			tail: result,
			tokens: [
				...head.tokens,
				collectedTokens.find(
					(t) => t.type === (op === "lambda" ? "=>" : "->"),
				)!,
				...result.tokens,
			], // approximate
		};
	}

	// For the whole expression, set tokens to all collected
	result.tokens = collectedTokens;
	return result;
}

export function parse_statement(tokens: TokenStream): Statement {
	// const ident = expect_token(tokens, "ident");
	const expr = parse_expression(tokens);
	expect_token(tokens, ":");
	const ty = parse_expression(tokens);
	let def = null;
	if (peek_token(tokens)?.type === ":=") {
		expect_token(tokens, ":=");
		def = parse_expression(tokens);
	}
	expect_token(tokens, ";");
	// statement should start with ident. first will error if not
	first_ident(expr);
	return { type: "statement", pat: expr, ty, def };
}

export function parse_program(tokens: TokenStream): Program {
	const dependencies: string[] = [];
	while (peek_token(tokens)?.type === "@require") {
		expect_token(tokens, "@require");
		const stringToken = expect_token(tokens, "string");
		dependencies.push(stringToken.value);
	}

	return {
		statements: parse_statements(tokens),
		dependencies,
	};
}

export function parse_statements(tokens: TokenStream): Statement[] {
	const stmts = [];
	while (peek_token(tokens) !== undefined) {
		stmts.push(parse_statement(tokens));
	}
	return stmts;
}

export function first_ident(expression: Expr): Expr & { type: "ident" } {
	while (expression.type === "application") {
		expression = expression.fun;
	}
	if (expression.type === "ident") {
		return expression;
	} else {
		throw new Error("not an ident");
	}
}

export function lex_all(text: string) {
	const tokens = [];
	let token;
	let start = 0;
	while (start < text.length) {
		[token, start] = lex(text, start);
		// if (token.type == "whitespace" || token.type == "comment") {
		// 	continue;
		// }
		tokens.push(token);
	}
	return tokens;
}
export function parse(text: string): Program {
	const tokens = lex_all(text);
	return parse_program({ tokens, cursor: 0 });
}
