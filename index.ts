import { file } from "bun";
import { check_program, new_globals } from "./check";
import { expand } from "./expand";
import { first_ident, type Statement } from "./parser";

// Checking is slow and uneven: most declarations are instant and a handful take
// most of the time, so this reports as it goes rather than at the end. A
// declaration slower than this gets a line of its own; --all times every one.
const SLOW_MS = 10;
const show_all = process.argv.includes("--all");

function duration(ms: number) {
	return ms >= 1000 ? `${(ms / 1000).toFixed(2)}s` : `${ms.toFixed(1)}ms`;
}

function row(label: string, ms: number, count?: number) {
	const stmts = count === undefined ? "" : `${String(count).padStart(4)} stmts`;
	return `  ${label.padEnd(30)} ${stmts.padStart(10)} ${duration(ms).padStart(8)}`;
}

// `Nat.Add` for a declaration, `Nat.rec rule` for one of its iota rules
function label_of(stmt: Statement) {
	const name = first_ident(stmt.pat).ident;
	return stmt.pat.type === "application" ? `${name} rule` : name;
}

function fail(where: string, e: unknown): never {
	console.error(`\n${where}: ${e instanceof Error ? e.message : String(e)}`);
	process.exit(1);
}

console.log("parse");
let parsed = 0;
// the file being read, so a parse error can say which one it was in
let reading = "";
const parse_started = performance.now();
let statements: Statement[];
try {
	statements = await expand(
		"./defs/main.txt",
		async (path) => {
			reading = path;
			return await file(path).text();
		},
		{
			on_parsed: (path, count, ms) => {
				parsed += count;
				console.log(row(path.replace("./defs/", ""), ms, count));
			},
		},
	);
} catch (e) {
	fail(`parse failed in ${reading}`, e);
}
const parse_ms = performance.now() - parse_started;
console.log(row("total", parse_ms, parsed));

console.log("check");
const times: { label: string; ms: number }[] = [];
const check_started = performance.now();
try {
	check_program(new_globals(), statements, {
		on_checked: (stmt, ms) => {
			const label = label_of(stmt);
			times.push({ label, ms });
			if (show_all || ms >= SLOW_MS) console.log(row(label, ms));
		},
	});
} catch (e) {
	// everything up to here checked, so the one that threw is the next one. A
	// throw from after the loop, like an incomplete set of iota rules, has none.
	const at = statements[times.length];
	fail(at ? `check failed at ${label_of(at)}` : "check failed", e);
}
const check_ms = performance.now() - check_started;

const slowest = [...times].sort((a, b) => b.ms - a.ms);
if (!show_all && slowest[0] !== undefined && slowest[0].ms < SLOW_MS) {
	// nothing was slow enough to have been mentioned already
	console.log(row(`slowest: ${slowest[0].label}`, slowest[0].ms));
}
console.log(row("total", check_ms, times.length));
console.log(
	`ok: ${parsed} statements in ${duration(parse_ms + check_ms)}` +
		(show_all ? "" : ", --all to time every one"),
);
