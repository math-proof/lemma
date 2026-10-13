/**
 * |M.env.R| / abs of a simple identifier → AbsR (glued), never Abs_R.
 * Run: `node mjs/lemmaPath.absR.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE = "Lemma/Random/NormClip/le/AbsR.lean";
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

const softLefts = [...new Set(
  r.suggestions
    .filter((s) => s.includes("/le/"))
    .map((s) => s.split("/le/")[0].replace(/^Random\//, "")),
)];

check("imply is NormClip/le/AbsR", r.imply.name === "NormClip/le/AbsR", `got ${r.imply.name}`);
check("imply right is AbsR", implyRight === "AbsR", `got ${implyRight}`);
check("top suggestion uses AbsR", r.suggestedPath === "Random/NormClip/le/AbsR.lean", `got ${r.suggestedPath}`);
check("Abs_R is not preferred", !r.suggestedPath.includes("Abs_R"), `got ${r.suggestedPath}`);
check("Abs_R not among soft /le/ rights", !softRights.includes("Abs_R"), `rights=${softRights.join(",")}`);
// Norm + clip glues (NormClip); contrast MEq_Clip — do not snake Norm_Clip
check("Norm_Clip is not preferred", !r.suggestedPath.includes("Norm_Clip"), `got ${r.suggestedPath}`);
check("Norm_Clip not among soft /le/ lefts", !softLefts.includes("Norm_Clip"), `lefts=${softLefts.join(",")}`);
check("current AbsR path is consistent", r.consistent.ok, JSON.stringify(r.consistent));

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
