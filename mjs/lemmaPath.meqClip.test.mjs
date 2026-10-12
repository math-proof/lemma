/**
 * Clip naming is context-dependent (not always snake, not always camel):
 *   MEq + clip  → MEq_Clip  (relational ae-eq; never MEqClip)
 *   Norm + clip → NormClip  (norm bound under /le/; never Norm_Clip)
 * Run: `node mjs/lemmaPath.meqClip.test.mjs`
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
  const FILE = "Lemma/Random/MEq_Clip/of/All_Eq.lean";
  const r = suggest(FILE);
  const implyHeads = [...new Set(r.suggestions.map((s) => s.split("/of/")[0].replace(/^Random\//, "")))];
  const hasMEqClip = implyHeads.some((h) => h.split("/").includes("MEqClip"));
  const hasMEq_Clip = implyHeads.some((h) => h.split("/").includes("MEq_Clip"));

  check("MEq: canon imply is MEq_Clip", r.imply.name === "MEq_Clip", `got ${r.imply.name}`);
  check(
    "MEq: top suggestion uses MEq_Clip",
    r.suggestedPath.startsWith("Random/MEq_Clip/"),
    `got ${r.suggestedPath}`,
  );
  check("MEq: suggestions include MEq_Clip", hasMEq_Clip, `heads=${implyHeads.slice(0, 6).join(",")}`);
  check(
    "MEq: suggestions never use camel MEqClip",
    !hasMEqClip,
    `heads=${implyHeads.filter((h) => h.includes("MEqClip")).join(",")}`,
  );
  check(
    "MEq: current MEq_Clip/of/All_Eq path is consistent",
    r.consistent.ok && r.currentPath.startsWith("Random/MEq_Clip/"),
    JSON.stringify(r.consistent),
  );
}

{
  const FILE = "Lemma/Random/NormClip/le/AbsR.lean";
  const r = suggest(FILE);
  const softLefts = [...new Set(
    r.suggestions
      .filter((s) => s.includes("/le/"))
      .map((s) => s.split("/le/")[0].replace(/^Random\//, "")),
  )];

  check("Norm: canon imply is NormClip/le/AbsR", r.imply.name === "NormClip/le/AbsR", `got ${r.imply.name}`);
  check(
    "Norm: top suggestion is NormClip/le/AbsR",
    r.suggestedPath === "Random/NormClip/le/AbsR.lean",
    `got ${r.suggestedPath}`,
  );
  check("Norm: never prefers Norm_Clip", !r.suggestedPath.includes("Norm_Clip"), `got ${r.suggestedPath}`);
  check(
    "Norm: Norm_Clip not among soft /le/ lefts",
    !softLefts.includes("Norm_Clip"),
    `lefts=${softLefts.join(",")}`,
  );
  check("Norm: current NormClip path is consistent", r.consistent.ok, JSON.stringify(r.consistent));
}

if (failed) {
  console.error(`${failed} failed`);
  process.exit(1);
}
console.log("all passed");
