/**
 * regression.mjs — hole-regex regression over `mjs/*.json` fixtures.
 *
 * Each fixture is `{ "lean": <Lean type expression>, "regex": [<expected>] }`.
 * The runner parses `lean` into the AST, generates the hole-regex alternatives
 * for that node, and requires an exact match with the fixture's `regex` list.
 *
 * Run: node mjs/regression.mjs
 */
import fs from "fs";
import path from "path";
import { fileURLToPath } from "url";
import { compile } from "../js/parser/lean.js";
import { strStmt } from "../js/parser/lean/utility.js";
import { holeRegexAlternatives } from "./lemmaPath.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const CLASS = (n) => n?.constructor?.name || "";

const norm = (s) => String(s || "")
  .split("\n")
  .filter((l) => !/^\s*--/.test(l))
  .join("\n")
  .replace(/\s+/g, "");
const loose = (s) => norm(s).replace(/[()]/g, "");

function findNodeByText(root, text) {
  const target = loose(text);
  if (!target) return null;
  let hit = null;
  (function walk(n) {
    if (hit || !n || typeof n !== "object") return;
    if (Array.isArray(n)) {
      for (const x of n) walk(x);
      return;
    }
    let s = "";
    try { s = strStmt(n); } catch { s = ""; }
    if (s && loose(s) === target) {
      hit = n;
      return;
    }
    for (const a of n.args || []) walk(a);
  })(root);
  return hit;
}

/**
 * Free identifiers of a standalone statement become holes: lowercase names
 * (`f`, `n`, `s`, `π`, …) and single uppercase letters (`X`, `Y`, `L`, …).
 * Numeric literals are kept literal.
 */
function collectLeaves(root) {
  const leaves = new Set();
  (function walk(n) {
    if (!n || typeof n !== "object") return;
    if (Array.isArray(n)) {
      for (const x of n) walk(x);
      return;
    }
    if (CLASS(n) === "LeanToken") {
      const text = n.text || "";
      if (!/^-?\d+$/.test(text) && (/^\p{Ll}/u.test(text) || /^[A-Z]$/.test(text))) leaves.add(text);
      return;
    }
    for (const a of n.args || []) walk(a);
  })(root);
  return leaves;
}

function parseStatement(lean) {
  const tree = compile(`private lemma main : ${lean} := by\n  sorry\n`);
  return findNodeByText(tree, lean);
}

let failures = 0;
let checked = 0;
const files = fs.readdirSync(__dirname).filter((f) => f.endsWith(".json")).sort();
for (const name of files) {
  const abs = path.join(__dirname, name);
  let doc;
  try {
    doc = JSON.parse(fs.readFileSync(abs, "utf8"));
  } catch (e) {
    failures++;
    console.log(`FAIL ${name}\n  invalid JSON: ${e.message}`);
    continue;
  }
  if (!doc || typeof doc.lean !== "string" || !Array.isArray(doc.regex)) {
    console.log(`skip ${name} (not a fixture)`);
    continue;
  }
  checked++;
  const fail = (msg) => {
    failures++;
    console.log(`FAIL ${name}\n  ${msg}`);
  };

  let node;
  try {
    node = parseStatement(doc.lean);
  } catch (e) {
    fail(`parse error: ${e.message}`);
    continue;
  }
  if (!node) {
    fail(`no AST node matches lean:\n  ${doc.lean}`);
    continue;
  }

  const got = holeRegexAlternatives(node, { leaves: collectLeaves(node) });
  if (JSON.stringify(got) !== JSON.stringify(doc.regex)) {
    fail(`regex mismatch\n  got:  ${JSON.stringify(got)}\n  want: ${JSON.stringify(doc.regex)}`);
    continue;
  }
  console.log(`OK   ${name}`);
}

console.log(`\n${failures === 0 ? "all passed" : failures + " failed"} (${checked} fixtures)`);
process.exit(failures === 0 ? 0 : 1);
