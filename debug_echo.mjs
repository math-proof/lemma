import fs from "fs";
import { echo2vueFromSource } from "./mjs/lean/compiler/index.mjs";
const abs = "/home/cosmos/src/lean/Lemma/WeierstrassCurve/Any_Eq_SMul.lean";
const source = fs.readFileSync(abs, "utf8");
console.log("start", Date.now());
const t = setInterval(() => console.log("tick", Date.now()), 5000);
try {
  const code = await echo2vueFromSource(source, { leanAbsPath: abs, module: "WeierstrassCurve.Any_Eq_SMul" });
  console.log("done errors", (code.error||[]).length, "warnings", (code.warning||[]).length);
  for (const e of (code.error||[]).slice(0,8)) console.log(e.line, (e.info||"").split("\n")[0]);
  if (!(code.error||[]).length) console.log("OK");
} catch (e) {
  console.error("fail", e);
} finally {
  clearInterval(t);
}
