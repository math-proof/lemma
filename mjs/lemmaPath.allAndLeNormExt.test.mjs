/**
 * ∀ᵐ ω, HasSum ∧ ‖((γ ^ id) @ r[t:]) ω‖ ≤ bound → All_And_LeNormExtDotPow_Id/of/All_Eq_Joint/In_Ico.
 * Run: `node mjs/lemmaPath.allAndLeNormExt.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE = "Lemma/Random/All_And_LeNormExtDotPow_Id/of/All_Eq_Joint/In_Ico.lean";
const WANT = "Random/All_And_LeNormExtDotPow_Id/of/All_Eq_Joint/In_Ico.lean";
let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

const r = suggest(FILE);
const heads = [...new Set(r.suggestions.map((s) => s.split("/of/")[0].replace(/^Random\//, "")))];

check("imply is All_And_LeNormExtDotPow_Id", r.imply.name === "All_And_LeNormExtDotPow_Id", `got ${r.imply.name}`);
check("top suggestion is exact path", r.suggestedPath === WANT, `got ${r.suggestedPath}`);
check("consistent yes", r.consistent.ok, JSON.stringify(r.consistent));
check("givens All_Eq_Joint + In_Ico", r.givensPathOrder.map((g) => g.name).join("/") === "All_Eq_Joint/In_Ico", r.givensPathOrder.map((g) => g.name).join("/"));
check("never prefers GetDot imply", !heads[0]?.includes("GetDot") && !r.suggestedPath.includes("GetDot"));
check("never prefers /le/MulSub1AbsR", !r.suggestedPath.includes("/le/MulSub1AbsR"));
check("never prefers of/All_Eq/ without Joint as top", !r.suggestedPath.includes("/of/All_Eq/In_Ico") || r.suggestedPath.includes("All_Eq_Joint"));

{
  const i = suggest("Lemma/Random/IntegrableDotPow_Id/of/All_Eq/In_Ico.lean");
  check("IntegrableDotPow_Id imply unchanged", i.imply.name === "IntegrableDotPow_Id", `got ${i.imply.name}`);
  check("IntegrableDotPow_Id has no GetDot", !i.suggestedPath.includes("GetDot"));
  check("IntegrableDotPow_Id has no Integrable_DotPow", !i.imply.name.includes("Integrable_DotPow"));
}

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
