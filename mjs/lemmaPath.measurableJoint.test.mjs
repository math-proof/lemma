/**
 * `Measurable (r, a, s)` / joint_rv → MeasurableJoint (accepted in path).
 * Run: `node mjs/lemmaPath.measurableJoint.test.mjs`
 */
import { suggest } from "./lemmaPath.mjs";

let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

{
  const file = "Lemma/Random/MEqExpectS/of/CondIndep/Integrable/MeasurableJoint/Measurable.lean";
  const r = suggest(file);
  const hr = r.givensLeanOrder.find((g) => g.binder === "hr");
  const hG = r.givensLeanOrder.find((g) => g.binder === "hG");
  check("joint hyp names MeasurableJoint", hr?.name === "MeasurableJoint", `got ${hr?.name}`);
  check("unary Measurable G stays Measurable", hG?.name === "Measurable", `got ${hG?.name}`);
  check("path with MeasurableJoint is consistent", r.consistent.ok, JSON.stringify(r.consistent));
  check(
    "best suggestion keeps MeasurableJoint",
    r.suggestedPath.includes("/MeasurableJoint/"),
    `got ${r.suggestedPath}`,
  );
}

{
  const file = "Lemma/Random/CondIndep/of/All_CondIndep/All_MeasurableJoint.lean";
  const r = suggest(file);
  check("All_MeasurableJoint path accepted", r.consistent.ok, JSON.stringify(r.consistent));
  const g = r.givensPathOrder.find((x) => /Measurable/.test(x.name));
  check("∀ Measurable (r t, s t, a t) → All_MeasurableJoint", /All_?MeasurableJoint/.test(g?.name || ""), `got ${g?.name}`);
}

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
