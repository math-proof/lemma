/**
 * Bellman ∧-chain: imply folders stay `MEq_Expect_*`, never camel `MEqExpect` / bare `MEq`.
 * Run: `node mjs/lemmaPath.meqExpectSnake.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

const FILE =
  "Lemma/Random/MEq_Expect_Cond/MEqExpect/MEq/of/MEqExpectS/All_MEq_Expect_CondDot/All_MEq_Expect_CondDot/GtInftySup/In_Ico.lean";

let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

const r = suggest(FILE);
const implyHeads = [...new Set(r.suggestions.map((s) => s.split("/of/")[0].replace(/^Random\//, "")))];
const badSeg = (h) =>
  h.split("/").some((c) => c === "MEq" || c === "MEqExpect" || /^MEqExpect(?!S(?:_|$))/.test(c));

check(
  "canon imply uses MEq_Expect_CondAdd_Mul chain",
  r.imply.name === "MEq_Expect_Cond/MEq_Expect_CondAdd_Mul/MEq_Expect_CondAdd_Mul",
  `got ${r.imply.name}`,
);
check(
  "top suggestion uses MEq_Expect_CondAdd_Mul",
  r.suggestedPath.includes("MEq_Expect_CondAdd_Mul"),
  `got ${r.suggestedPath}`,
);
check(
  "top suggestion has no MEqExpect / bare MEq imply folders",
  !badSeg(r.suggestedPath.split("/of/")[0].replace(/^Random\//, "")),
  `got ${r.suggestedPath}`,
);
check(
  "no suggested imply head uses MEqExpect or bare MEq",
  implyHeads.every((h) => !badSeg(h)),
  `bad: ${implyHeads.filter(badSeg).slice(0, 5).join(" | ")}`,
);
check(
  "current camel/bare-MEq path is inconsistent",
  !r.consistent.ok,
  JSON.stringify(r.consistent),
);
check(
  "givens path order keeps MEqExpectS + CondDotPow ×2 + GtInftySup + MeasurableJoint + In_Ico",
  r.givensPathOrder.map((g) => g.name).join("/") ===
    "MEqExpectS/All_MEq_Expect_CondDotPow/All_MEq_Expect_CondDotPow/GtInftySup/All_MeasurableJoint/In_Ico",
  r.givensPathOrder.map((g) => g.name).join("/"),
);

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
