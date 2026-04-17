import { parse, type Statement } from "./parser";

export async function expand(
	entry: string,
	load: (path: string) => string | Promise<string>,
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
		const { statements, dependencies } = parse(text);

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
