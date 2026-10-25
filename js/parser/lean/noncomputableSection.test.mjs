/**
 * noncomputable / partial / unsafe section must parse (push_accessibility Lean_section).
 * Run: node js/parser/lean/noncomputableSection.test.mjs
 */
import { compile } from "../lean.js";

let failed = 0;
function check(name, cond, detail = "") {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ": " + detail : ""}`);
  } else console.log(`ok   ${name}`);
}

function topKinds(src) {
  const ast = compile(src);
  return (ast.args || []).map((a) => ({
    kind: a.constructor.name,
    acc: a.accessibility || "public",
  }));
}

{
  const ks = topKinds("import Mathlib\nsection\nlemma foo : True := by trivial\nend\n");
  check("plain section is Lean_section", ks.some((k) => k.kind === "Lean_section"));
}
{
  const ks = topKinds("import Mathlib\nnoncomputable section\nlemma foo : True := by trivial\nend\n");
  const sec = ks.find((k) => k.kind === "Lean_section");
  check("noncomputable section parses", !!sec);
  check("noncomputable accessibility", !!sec && sec.acc === "noncomputable", sec && sec.acc);
}
{
  const ks = topKinds("import Mathlib\nnoncomputable section Foo\nlemma foo : True := by trivial\nend Foo\n");
  const sec = ks.find((k) => k.kind === "Lean_section");
  check("named noncomputable section", !!sec && sec.acc === "noncomputable");
}
{
  const ks = topKinds("import Mathlib\npartial section\nlemma foo : True := by trivial\nend\n");
  const sec = ks.find((k) => k.kind === "Lean_section");
  check("partial section", !!sec && sec.acc === "partial");
}
{
  const ks = topKinds("import Mathlib\nunsafe section\nlemma foo : True := by trivial\nend\n");
  const sec = ks.find((k) => k.kind === "Lean_section");
  check("unsafe section", !!sec && sec.acc === "unsafe");
}

if (failed) {
  console.error(failed + " failed");
  process.exit(1);
}
console.log("all passed");
