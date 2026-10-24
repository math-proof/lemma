import { echo2vueFromSource } from "./mjs/lean/compiler/index.mjs";
import fs from "fs";

const files = [
  "Lemma/Int/SMulLiftKaehlerDifferential.lean",
  "Lemma/Int/OrthogonalSum/eq/Add.lean",
  "Lemma/Int/Pow/eq/OneOrEqPow/of/EqMul_1.lean",
  "Lemma/Int/Level1/ne/Top.lean",
  "Lemma/Int/Eq_1/of/IsUnit.lean",
];
for (const f of files) {
  const src = fs.readFileSync(f, "utf8");
  try {
    const r = echo2vueFromSource(src, f);
    console.log("OK", f, "keys", Object.keys(r||{}).slice(0,8));
  } catch (e) {
    console.log("ERR", f, e.message.split("\n")[0]);
  }
}
