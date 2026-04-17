import { createRoot } from "react-dom/client";
import { check_program, new_globals } from "../check";
import { lex_all, parse, type Token } from "../parser";
import { levels } from "./levels";
import { useEffect, useRef, useState } from "react";
import { expand } from "../expand";

import Editor from "@monaco-editor/react";
import { libs } from "./libs";

const root = createRoot(document.getElementById("root")!);

const Render = ({
	text,
	on_change,
	show_hints,
}: {
	text: string;
	on_change?: (text: string) => void;
	show_hints?: boolean;
}) => {
	const fragments = [];
	const inputs = useRef<{ value: string }[]>([]);

	const reconstruct = () => {
		let result = text;
		let i = 0;
		result = result.replace(/<INPUT>|<BLOCK>/g, (input) => {
			const val = inputs.current[i]?.value ?? "<EMPTY>";
			i++;
			return val;
		});
		return result;
	};

	const renderTokens = (tokens: Token[], l: number) => {
		return tokens.map((token, index) => {
			let toktype;
			if (token.type === "ident") {
				if (token.raw.match(/^[0-9]+$/)) {
					toktype = "number";
				} else {
					toktype = "ident";
				}
			} else if (["=>", "->", ":=", ":", ";"].includes(token.type)) {
				toktype = "symbol";
			} else if (["(", ")"].includes(token.type)) {
				toktype = "parentheses";
			} else if (token.type === "comment") {
				toktype = "comment";
			} else if (token.type === "string") {
				toktype = "string";
			} else if (token.type === "@require") {
				toktype = "directive";
			}
			return (
				<span key={`${l}-${index}`} className={toktype}>
					{token.raw}
				</span>
			);
		});
	};

	let l = 0;
	let tail = text;
	let start = 0;
	for (const match of text.matchAll(/<INPUT>|<BLOCK>/g)) {
		const before = text.substring(start, match.index);
		const after = text.substring(match.index + match[0].length);
		start = match.index + match[0].length;
		const tokens = lex_all(before);
		fragments.push(...renderTokens(tokens, l));
		if (match[0] === "<INPUT>") {
			((i) => {
				fragments.push(
					<input
						key={`input-${i}`}
						ref={(input) => {
							if (!input) return;

							inputs.current[i] = input;
						}}
						onChange={(e) => {
							on_change?.(reconstruct());
						}}
					/>,
				);
			})(l);
			l++;
		} else if (match[0] === "<BLOCK>") {
			((i) => {
				fragments.push(
					<Editor
						theme="vs-dark"
						width={800}
						height={1000}
						key={`input-${i}`}
						onMount={(editor, monaco) => {
							inputs.current[i] = {
								value: editor.getValue() ?? "",
							};
						}}
						onChange={(value, ev) => {
							if (inputs.current[i]) {
								inputs.current[i]!.value = value ?? "";
								on_change?.(reconstruct());
							}
						}}
					/>,
				);
			})(l);
			l++;
		}
		tail = after;
	}
	inputs.current.length = l;
	const tail_tokens = lex_all(tail);
	fragments.push(...renderTokens(tail_tokens, l));

	on_change?.(reconstruct());
	return <code data-show-hints={show_hints}>{fragments}</code>;
};

const Main = () => {
	const [output, set_output] = useState<string | Error>("");
	// const [level_num, set_level_num] = useState(0);
	const params = new URLSearchParams(window.location.search);
	const [level_num, set_level_num] = useState(
		Number(params.get("level")) || 0,
	);
	const [show_hints, set_show_hints] = useState(false);
	const level = levels[level_num]!;
	const [successful, set_successful] = useState(false);
	const text = useRef<string>("");
	useEffect(() => {
		window.addEventListener("popstate", (event) => {
			const params = new URLSearchParams(window.location.search);
			const level = Number(params.get("level")) || 0;
			set_level_num(level);
			set_output("");
			set_successful(false);
			set_show_hints(false);
		});
	}, []);

	return (
		<main>
			<h2>Level {level_num + 1}</h2>
			<Render
				text={level}
				show_hints={show_hints}
				on_change={(value) => {
					console.log(value);
					text.current = value;
				}}
			/>
			<div className="output" data-successful={successful}>
				{output instanceof Error ? output.message : output}
			</div>
			<div className="button-container">
				<button
					onClick={async () => {
						const globals = new_globals();
						try {
							const statements = await expand(
								"main",
								async (path) => {
									if (path === "main") return text.current;
									if (!libs[path]) {
										throw new Error(
											`No such file: ${path}`,
										);
									}
									return libs[path];
								},
							);

							check_program(globals, statements);

							set_output("Well done!");
							set_successful(true);
						} catch (e: unknown) {
							set_output(e as Error);
						}
					}}
				>
					Check
				</button>
				<button onClick={() => set_show_hints(!show_hints)}>
					{show_hints ? "Hide hints" : "Show hints"}
				</button>
				<button
					hidden={level_num === 0}
					onClick={() => {
						set_successful(false);
						set_output("");
						history.pushState(
							null,
							"",
							`${window.location.pathname}?level=${level_num - 1}`,
						);
						set_level_num(level_num - 1);
						set_show_hints(false);
					}}
				>
					Previous level
				</button>
				<button
					hidden={!successful || level_num === levels.length - 1}
					onClick={() => {
						// set_level_num(level_num + 1);
						set_successful(false);
						set_output("");
						history.pushState(
							null,
							"",
							`${window.location.pathname}?level=${level_num + 1}`,
						);
						set_level_num(level_num + 1);
						set_show_hints(false);
					}}
				>
					Next level
				</button>
			</div>
		</main>
	);
};
root.render(<Main />);
