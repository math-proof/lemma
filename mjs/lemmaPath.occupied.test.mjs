/**
 * Sibling rename collision: action / reward / state Measurable lemmas share `All_Eq`.
 * Occupied paths rank below free ones. Run: `node mjs/lemmaPath.occupied.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const TAKEN = "Random/Measurable/of/All_Eq.lean";
let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

{
  const action = suggest("Lemma/Random/Measurable/of/All_Eq.lean");
  check(
    "action lemma may keep its own occupied path as best",
    action.suggestedPath === TAKEN,
    `got ${action.suggestedPath}`,
  );
  check("action current matches All_Eq", action.currentPath === TAKEN);
}

for (const [label, file] of [
  ["reward", "Lemma/Random/Measurable_R.lean"],
  ["state", "Lemma/Random/Measurable_S.lean"],
]) {
  const r = suggest(file);
  check(
    `${label}: best is not occupied All_Eq`,
    r.suggestedPath !== TAKEN,
    `got ${r.suggestedPath}`,
  );
  check(
    `${label}: All_Eq still listed but demoted`,
    r.suggestions.includes(TAKEN) && r.suggestions.indexOf(TAKEN) > 0,
    `idx=${r.suggestions.indexOf(TAKEN)} top=${r.suggestions[0]}`,
  );
  const freeIdx = r.suggestions.findIndex((s) => s !== TAKEN);
  const takenIdx = r.suggestions.indexOf(TAKEN);
  check(
    `${label}: some free path ranks above All_Eq`,
    freeIdx >= 0 && freeIdx < takenIdx,
    `freeIdx=${freeIdx} takenIdx=${takenIdx}`,
  );
}

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
