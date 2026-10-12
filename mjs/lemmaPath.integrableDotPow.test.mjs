/**
 * Integrable ((γ ^ id) @ r[t:]) → IntegrableDotPow_Id, not Integrable_DotPow_Id.
 * Run: `node mjs/lemmaPath.integrableDotPow.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE = "Lemma/Random/IntegrableDotPow_Id/of/All_Eq/In_Ico.lean";
let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

const r = suggest(FILE);
const heads = [...new Set(r.suggestions.map((s) => s.split("/of/")[0].replace(/^Random\//, "")))];

check("imply is IntegrableDotPow_Id", r.imply.name === "IntegrableDotPow_Id", `got ${r.imply.name}`);
check("top suggestion IntegrableDotPow_Id", r.suggestedPath.startsWith("Random/IntegrableDotPow_Id/"), `got ${r.suggestedPath}`);
check("never prefers Integrable_DotPow_Id", !r.suggestedPath.includes("Integrable_DotPow_Id"));
check("Integrable_DotPow_Id not among imply heads", !heads.includes("Integrable_DotPow_Id"), `heads has it`);
check("current path consistent", r.consistent.ok, JSON.stringify(r.consistent));

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
