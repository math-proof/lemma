import { compile } from "../../../js/parser/lean.js";
import "../../../js/py.js";
import fs from "fs";
import { homedir } from "os";
import path from "path";

function tryCompile(label, src) {
  try {
    compile(src);
    console.log("OK", label);
  } catch (e) {
    console.log("ERR", label, "=>", e.message.split("\n")[0]);
  }
}

const src = fs.readFileSync(path.join(homedir(), "src/lean/Lemma/Int/Level1/ne/Top.lean"), "utf8");
tryCompile("level1-full", src);

// only first lemma
const firstOnly = src.split("/--\n[VermaJantzenFiltration.level_one_max]")[0] + "\n\n-- created on 2026-10-23\n";
tryCompile("level1-first-only", firstOnly);

// first lemma with := by
let t = firstOnly.replace(
  "  filt.level 1 ≠ ⊤ :=\n-- proof\n  filt.level_one_is_maximal.1",
  "  filt.level 1 ≠ ⊤ := by\n-- proof\n  exact filt.level_one_is_maximal.1"
);
tryCompile("level1-first-by", t);

// both lemmas but with := by on first
t = src.replace(
  "  filt.level 1 ≠ ⊤ :=\n-- proof\n  filt.level_one_is_maximal.1",
  "  filt.level 1 ≠ ⊤ := by\n-- proof\n  exact filt.level_one_is_maximal.1"
).replace(
  "  N ≤ filt.level 1 :=\n-- proof\n  filt.level_one_is_maximal.2 N hN",
  "  N ≤ filt.level 1 := by\n-- proof\n  exact filt.level_one_is_maximal.2 N hN"
);
tryCompile("level1-both-by", t);

// private both
t = src.replaceAll("@[path]\nlemma ", "@[path]\nprivate lemma ");
tryCompile("level1-private", t);

// := by + private
t = src.replaceAll("@[path]\nlemma ", "@[path]\nprivate lemma ")
  .replace(
  "  filt.level 1 ≠ ⊤ :=\n-- proof\n  filt.level_one_is_maximal.1",
  "  filt.level 1 ≠ ⊤ := by\n-- proof\n  exact filt.level_one_is_maximal.1"
).replace(
  "  N ≤ filt.level 1 :=\n-- proof\n  filt.level_one_is_maximal.2 N hN",
  "  N ≤ filt.level 1 := by\n-- proof\n  exact filt.level_one_is_maximal.2 N hN"
);
tryCompile("level1-private-by", t);
