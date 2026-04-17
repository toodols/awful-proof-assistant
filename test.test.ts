import { test, expect } from "bun:test";
import { parse } from "./parser";

test("test", async () => {
	const equality_defs = await Bun.file("./defs/equality").text();
	const result = parse(equality_defs);
});

test("parse_directive", () => {
	const source = `
	@require "prop"
	`;

	const result = parse(source);
	expect(result.dependencies).toEqual(["prop"]);
});
