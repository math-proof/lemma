import fs from "fs";
import { execFileSync } from "child_process";

const kinds = JSON.parse(fs.readFileSync("/tmp/section_kinds.json", "utf8"));
const kindOf = Object.fromEntries(kinds.map((k) => [k.folder, k.kind]));
const DATA = new Set(kinds.filter((k) => k.kind === "data type").map((k) => k.folder));

const files = `
Lemma/IsAlgClosed/All_Any_EqCompValHopfKer/of/Surjective.lean
Lemma/IsAlgClosed/AnyIsKleinDatum/of/AddMul4PowMul27PowNe0.lean
Lemma/IsAlgClosed/Any_All_EqResidueR.lean
Lemma/IsAlgClosed/Any_And_All_Eq_SMul/of/Pairwise_Commute.lean
Lemma/IsAlgClosed/Any_And_Eq_AddPowSubXCC/of/Ne_0/GtNatDegree0/EqNatDegree/Monic/Ge_2/NeK0.lean
Lemma/IsAlgClosed/Any_And_IsUnitAndAll_Algebra/of/IsUnit.lean
Lemma/IsAlgClosed/Any_And_Ne_1AndEqLegendreJ/of/NeK0.lean
Lemma/IsAlgClosed/Any_EqToSubringToValuationSubring/of/Ne_Top/All_InAlgebraMap/IsIntegrallyClosedInR.lean
Lemma/IsAlgClosed/Any_InSub_AlgebraMapNonunitsToValuationSubring/of/In_ToValuationSubring.lean
Lemma/IsAlgClosed/Any_IsKleinDatum/of/NeAddMul4Pow_3Mul27Square_0.lean
Lemma/IsAlgClosed/CardRootsFibrePoly/eq/NatDegree/of/Monic.lean
Lemma/IsAlgClosed/Eq/of/EqSndPullbackLimits_ToBase/IsIso.lean
Lemma/IsAlgClosed/EqComp/of/Surjective.lean
Lemma/IsAlgClosed/Eq_Comp/of/Surjective.lean
Lemma/IsAlgClosed/HenselianLocalRing.lean
Lemma/IsAlgClosed/InSubAlgebraMapNonunits/of/InToValuationSubring.lean
Lemma/IsAlgClosed/Injective/of/All_NeMul_SquareAlgebraMapK/Commute/Ne_0/InjectiveAlgebraMapK.lean
Lemma/IsAlgClosed/IsPoleFreeOnAndDegreeNum/lt/DegreeDenAndIsPoleFreeOnAndAll_EqEvalAtAddEvalSAt/of/Ne_0.lean
Lemma/IsAlgClosed/NonemptyAffinoid/of/Any_All_Any_LtUFnSubPowV.lean
Lemma/IsAlgClosed/PointEnd/eq/SymmPointEquivPlace_RestrictAlongPlaceOfPointH/of/NormFormulaAlongHfin.lean
Lemma/IsAlgClosed/PointHom/eq/SymmPointEquivPlace/of/NormFormulaAlong.lean
Lemma/IsAlgClosed/PointHom/eq/SymmPointEquivPlace_W_RestrictAlongPlaceOfPointH/of/NormFormulaAlongHfin.lean
Lemma/IsAlgClosed/ResidueField/Any_InAMaximalIdealAndAll_NeEval0.lean
Lemma/IsAlgClosed/SubAlgebraMapInNonunits/of/InToValuationSubring.lean
Lemma/IsAlgClosed/exists/AlgEquiv/Apply/ne/of/NotMem/Range.lean
`.trim().split("\n");

const rows = [];
for (const f of files) {
  let r;
  try {
    let raw = execFileSync("node", ["mjs/lemmaPath.mjs", "--json", f], {
      encoding: "utf8",
      maxBuffer: 50 * 1024 * 1024,
    });
    raw = raw.replace(/^import py\.js\n/, "");
    r = JSON.parse(raw);
  } catch (e) {
    const msg = String(e.stderr || e.message || e).slice(0, 400);
    rows.push({ file: f, error: msg });
    console.log("ERR", f, msg.slice(0, 120));
    continue;
  }
  const sug = r.suggestedPath || "";
  const sec = sug.split("/")[0];
  const kind = kindOf[sec] || "missing";
  const legal = kind === "data type";
  // candidate data-type sections from tokens
  const dataToks = (r.sectionTokens || []).filter((t) => DATA.has(t));
  rows.push({
    file: f.replace(/^Lemma\//, ""),
    suggested: sug,
    section: r.section,
    sectionScore: r.sectionScore,
    kind,
    legal,
    consistentOk: r.consistent?.ok,
    reason: r.consistent?.reason,
    dataTokens: dataToks,
    tokens: r.sectionTokens || [],
  });
  console.log((legal ? "OK" : "BAD"), f.replace("Lemma/", ""), "->", sug, "(" + kind + ")", "dataToks=" + dataToks.join(","));
}
fs.writeFileSync("/tmp/isalg_map.json", JSON.stringify(rows, null, 2));
console.log("wrote", rows.length, "rows");
