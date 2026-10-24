import fs from "fs";
import "../js/py.js";
import { compile } from "./js/parser/lean.js";

const abs = "./Lemma/WeierstrassCurve/Any_Eq_SMul.lean";
const source = fs.readFileSync(abs, "utf8");
console.log("compile start");
const tree = compile(source);
console.log("compile done");
tree.relocate_last_comment();
console.log("echo inject");
tree.echo();
console.log("stringify");
const codeStr = String(tree);
console.log("len", codeStr.length);
fs.writeFileSync("/tmp/any_ast_echo.lean", codeStr);
console.log("wrote");
