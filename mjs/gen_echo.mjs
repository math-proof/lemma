import fs from "fs";
import "../js/py.js";
import { compile } from "../js/parser/lean.js";

const abs = "/home/cosmos/src/lean/Lemma/WeierstrassCurve/Any_Eq_SMul.lean";
const source = fs.readFileSync(abs, "utf8");
console.log("compile");
const tree = compile(source);
console.log("echo");
tree.relocate_last_comment();
tree.echo();
const codeStr = String(tree);
const out = "/home/cosmos/src/lean/Lemma/WeierstrassCurve/Any_Eq_SMul.echo.lean";
fs.writeFileSync(out, codeStr);
console.log("wrote", "lines", codeStr.split("\n").length);
