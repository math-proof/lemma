/**
 * |M.env.R| / abs of a simple identifier → AbsR (glued), never Abs_R.
 * Run: `node mjs/lemmaPath.absR.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE = "Lemma/Random/NormRc/le/AbsR.lean";
let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

const r = suggest(FILE);
const implyRight = r.imply.name.split("/").pop();
const softRights = [...new Set(
  r.suggestions
    .filter((s) => s.includes("/le/"))
    .map((s) => s.split("/le/")[1]?.replace(/\.lean$/, "")),
)];

check("imply is NormRc/le/AbsR", r.imply.name === "NormRc/le/AbsR", `got ${r.imply.name}`);
check("imply right is AbsR", implyRight === "AbsR", `got ${implyRight}`);
check("top suggestion uses AbsR", r.suggestedPath === "Random/NormRc/le/AbsR.lean", `got ${r.suggestedPath}`);
check("Abs_R is not preferred", !r.suggestedPath.includes("Abs_R"), `got ${r.suggestedPath}`);
check("Abs_R not among soft /le/ rights", !softRights.includes("Abs_R"), `rights=${softRights.join(",")}`);
check("current AbsR path is consistent", r.consistent.ok, JSON.stringify(r.consistent));

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
