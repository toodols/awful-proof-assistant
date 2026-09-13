import { parse, type Statement } from "./parser";

export type ExpandOptions = {
	// called as each file is read and parsed, innermost dependency first, so a
	// caller can report where the time went and how far it got
	on_parsed?: (path: string, statements: number, ms: number) => void;
};

export async function expand(
	entry: string,
	load: (path: string) => string | Promise<string>,
	opts: ExpandOptions = {},
): Promise<Statement[]> {
	const visited = new Set<string>();
	const visiting = new Set<string>();
	const all: Statement[] = [];

	function dir_of(path: string) {
		return path.substring(0, path.lastIndexOf("/") + 1);
	}

	function join(dir: string, file: string) {
		if (file.startsWith("/")) return file;
		return dir + file;
	}

	async function process(path: string) {
		if (visiting.has(path)) {
			throw new Error(`Circular dependency detected: ${path}`);
		}
		if (visited.has(path)) return;

		visiting.add(path);

		const text = await load(path);
		const started = performance.now();
		const { statements, dependencies } = parse(text);
		opts.on_parsed?.(path, statements.length, performance.now() - started);

		const dir = dir_of(path);

		for (const dep of dependencies) {
			await process(join(dir, dep));
		}

		visiting.delete(path);
		visited.add(path);

		all.push(...statements);
	}

	await process(entry);

	return all;
}
