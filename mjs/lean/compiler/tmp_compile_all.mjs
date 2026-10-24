import { compile } from "../../../js/parser/lean.js";
import "../../../js/py.js";
import fs from "fs";

const files = fs.readFileSync("/tmp/group_int_files.txt","utf8").trim().split(/\n/);
let ok=0, bad=[];
for (const f of files) {
  try {
    compile(fs.readFileSync(f,"utf8"));
    ok++;
  } catch (e) {
    bad.push([f, e.message.split("\n")[0]]);
  }
}
console.log(`parse_ok ${ok}/${files.length}`);
for (const [f,m] of bad) console.log("ERR", f, m);
