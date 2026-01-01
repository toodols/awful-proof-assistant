export type Expr =
	| {
			type: "pi";
			head: Expr;
			tail: Expr;
	  }
	| {
			type: "lambda";
			head: Expr;
			tail: Expr;
	  }
	| {
			type: "application";
			fun: Expr;
			value: Expr;
	  }
	| {
			type: "ident";
			ident: string;
	  }
	| {
			type: "error";
	  }
	| {
			type: "ref";
			index: number;
	  }
	| {
			type: "binding";
			ident: string;
			ty: Expr;
	  };

export type Statement = {
	type: "statement";
	ident: string;
	ty: Expr;
	def: Expr | null;
};

type Token =
	| { type: "ident"; ident: string }
	| { type: "=>" | "->" | ":=" | "(" | ")" | ":" | ";" }
	| { type: "whitespace" }
	| { type: "comment"; comment: string };

export function lex(text: string, start: number): [Token, number] {
	const ident_regex = /[A-Za-z0-9\._]+/y;
	ident_regex.lastIndex = start;
	let ident = ident_regex.exec(text);
	if (ident) {
		return [{ type: "ident", ident: ident[0] }, start + ident[0].length];
	}
	const ws_regex = /[\t\r\n ]+/y;
	ws_regex.lastIndex = start;
	let ws = ws_regex.exec(text);
	if (ws) {
		return [{ type: "whitespace" }, start + ws[0].length];
	}

	const line_cmt_regex = /\/\/[^\n]*/y;
	line_cmt_regex.lastIndex = start;
	let line_cmt = line_cmt_regex.exec(text);
	if (line_cmt) {
		return [
			{ type: "comment", comment: line_cmt[0] },
			start + line_cmt[0].length,
		];
	}

	const block_cmt_regex = /\/\*([^\*]|\*[^\/])*\*\//y;
	block_cmt_regex.lastIndex = start;
	let block_cmt = block_cmt_regex.exec(text);
	if (block_cmt) {
		return [
			{ type: "comment", comment: block_cmt[0] },
			start + block_cmt[0].length,
		];
	}

	const ops = ["=>", "->", ":=", "(", ")", ":", ";"] as const;
	for (const op of ops) {
		if (text.startsWith(op, start)) {
			return [
				{
					type: op,
				},
				start + op.length,
			];
		}
	}
	console.log(text.slice(0, start));
	throw new Error("lexer consumed no input");
}

type TokenStream = {
	tokens: Token[];
	cursor: number;
};

export function expect_token<T extends Token["type"]>(
	tokens: TokenStream,
	type: T
) {
	const token = tokens.tokens[tokens.cursor];
	if (!token) {
		throw new Error(`expected ${type} but got EOF`);
	}
	if (token.type !== type) {
		console.log(tokens.tokens.slice(0, tokens.cursor));
		throw new Error(`expected ${type} but got ${token.type}`);
	}
	tokens.cursor += 1;
	return token as Token & { type: T };
}

export function next_token(tokens: TokenStream) {
	const token = tokens.tokens[tokens.cursor];
	tokens.cursor += 1;
	return token;
}

export function peek_token(tokens: TokenStream) {
	const token = tokens.tokens[tokens.cursor];
	return token;
}

export function parse_atom(tokens: TokenStream): Expr {
	if (peek_token(tokens)?.type === "(") {
		expect_token(tokens, "(");
		let res;
		// if the next two tokens are ident and :, treat this as a named binding
		// else it is just a regular expression inside parentheses
		if (
			tokens.tokens[tokens.cursor]?.type === "ident" &&
			tokens.tokens[tokens.cursor + 1]?.type === ":"
		) {
			const ident = expect_token(tokens, "ident");
			expect_token(tokens, ":");
			const expr = parse_expression(tokens);
			res = { type: "binding", ident: ident.ident, ty: expr } as const;
		} else {
			res = parse_expression(tokens);
		}
		expect_token(tokens, ")");
		return res;
	} else if (peek_token(tokens)?.type === "ident") {
		const ident = expect_token(tokens, "ident");
		return { type: "ident", ident: ident.ident };
	}
	throw new Error("cant");
}

// a -> b -> c = a -> (b -> c)
// a -> b => c
// -> is right associative
// a b c = (a b) c
// application  is left associative
// application has higher precedence than application
export function parse_expression(tokens: TokenStream): Expr {
	const tail: Expr[] = [];
	const ops = [];
	const expr = parse_atom(tokens);
	while (true) {
		// if the next token is an ident or (, op is application and parse an atom
		if (
			peek_token(tokens)?.type === "ident" ||
			peek_token(tokens)?.type === "("
		) {
			tail.push(parse_atom(tokens));
			ops.push("application");
		}
		// if the next token is a =>, op is lambda and parse an atom
		else if (peek_token(tokens)?.type === "=>") {
			expect_token(tokens, "=>");
			tail.push(parse_atom(tokens));
			ops.push("lambda");
		}
		// if the next token is a ->, op is pi and parse an atom
		else if (peek_token(tokens)?.type === "->") {
			expect_token(tokens, "->");
			tail.push(parse_atom(tokens));
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
		};
	}

	return result;
}

export function parse_statement(tokens: TokenStream): Statement {
	const ident = expect_token(tokens, "ident");
	expect_token(tokens, ":");
	const ty = parse_expression(tokens);
	let def = null;
	if (peek_token(tokens)?.type === ":=") {
		expect_token(tokens, ":=");
		def = parse_expression(tokens);
	}
	expect_token(tokens, ";");
	return { type: "statement", ident: ident.ident, ty, def };
}

export function parse_statements(tokens: TokenStream): Statement[] {
	const stmts = [];
	while (tokens.cursor < tokens.tokens.length) {
		stmts.push(parse_statement(tokens));
	}
	return stmts;
}

export function parse(text: string) {
	let start = 0;
	const tokens = [];
	let token;
	while (start < text.length) {
		[token, start] = lex(text, start);
		if (token.type == "whitespace" || token.type == "comment") {
			continue;
		}
		tokens.push(token);
	}
	return parse_statements({ tokens, cursor: 0 });
}
