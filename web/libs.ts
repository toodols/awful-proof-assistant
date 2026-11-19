import equality from "../cic/equality.txt";
import nat from "../cic/nat.txt";
import prop from "../cic/prop.txt";

export const libs: Record<string, string | undefined> = {
	"equality.txt": equality,
	"nat.txt": nat,
	"prop.txt": prop,
};
