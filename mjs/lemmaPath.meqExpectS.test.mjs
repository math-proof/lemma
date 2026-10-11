/**
 * σ-algebra 𝔼[…|…] =ᵐ 𝔼[…|…] → MEqExpectS, never MEqExpect_Expect_Cond.
 * Run: `node mjs/lemmaPath.meqExpectS.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE = "Lemma/Random/MEqExpectS/of/CondIndep/Integrable/MeasurableJoint/Measurable.lean";
let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

const r = suggest(FILE);
const heads = [...new Set(r.suggestions.map((s) => s.split("/of/")[0].replace(/^Random\//, "")))];

check("canon imply is MEqExpectS", r.imply.name === "MEqExpectS", `got ${r.imply.name}`);
check("best suggestion uses MEqExpectS", r.suggestedPath.startsWith("Random/MEqExpectS/"), `got ${r.suggestedPath}`);
check("never suggests MEqExpect_Expect_Cond", !heads.includes("MEqExpect_Expect_Cond"));
check("keeps MEqExpect among alts", heads.includes("MEqExpect"));
check(
  "snake MEq_Expect_Cond (not camel MEqExpect_Cond)",
  heads.includes("MEq_Expect_Cond") || heads.includes("MEqExpectS_Cond"),
  `heads=${heads.slice(0, 8).join(",")}`,
);
check("never suggests camel MEqExpect_Cond", !heads.includes("MEqExpect_Cond"));
check(
  "current MEqExpectS path still accepted",
  r.consistent.ok && r.currentPath.startsWith("Random/MEqExpectS/"),
  JSON.stringify(r.consistent),
);

// legacy short folder `MEqExpect` remains an accepted alt (not an illegal camel collapse)
{
  const legacy = suggest("Lemma/Random/MEqExpect/of/CondIndep/Integrable/Measurable/All_Measurable.lean");
  const legHeads = [...new Set(legacy.suggestions.map((s) => s.split("/of/")[0].replace(/^Random\//, "")))];
  check("legacy MEqExpect still among alts", legHeads.includes("MEqExpect"));
  check(
    "legacy MEqExpect path still accepted",
    legacy.consistent.ok && legacy.currentPath.startsWith("Random/MEqExpect/"),
    JSON.stringify(legacy.consistent),
  );
}

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
