/**
 * ∀ᵐ ω, ∀ k, ‖r k ω‖ ≤ |R| → All_LeNorm_Abs/of/All_Eq_Joint (not AeNorm/le/AbsR).
 * Run: `node mjs/lemmaPath.allLeNormAbs.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE = "Lemma/Random/All_LeNorm_Abs/of/All_Eq_Joint.lean";
const WANT = "Random/All_LeNorm_Abs/of/All_Eq_Joint.lean";
let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

const r = suggest(FILE);
check("imply is All_LeNorm_Abs", r.imply.name === "All_LeNorm_Abs", `got ${r.imply.name}`);
check("top suggestion exact", r.suggestedPath === WANT, `got ${r.suggestedPath}`);
check("consistent yes", r.consistent.ok, JSON.stringify(r.consistent));
check("givens All_Eq_Joint", r.givensPathOrder.map((g) => g.name).join("/") === "All_Eq_Joint");
check("not AeNorm/le/AbsR", !r.suggestedPath.includes("AeNorm") && !r.suggestedPath.includes("/le/Abs"));
check("not Abs_R imply", !r.imply.name.includes("Abs_R") && !r.imply.name.includes("AbsR"));

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
