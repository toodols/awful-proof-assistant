import { file } from "bun";
import { check_program, new_globals } from "./check";
import { expand } from "./expand";

const statements = await expand(
	"./defs/main.txt",
	async (path) => await file(path).text(),
);

const defs = new_globals();

check_program(defs, statements);
