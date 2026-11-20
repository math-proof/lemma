/**
 * regression.mjs — JSON / hole-regex regression over `mjs/regression/*.json`.
 *
 * Each fixture is `{ "lean": <Lean type expression>, "regex": <hole regex>,
 * "plural": [...], "json": <LeanNode.toJSON()> }`.
 *
 * Two independent, read-only checks per fixture:
 *   1. `json`  — parse `lean`, locate the statement node, and require its
 *      `toJSON()` to deep-equal the stored `json` field (key order ignored).
 *   2. `regex` — require `json2regex(stored json)` to equal `regex`.
 *
 * The runner never writes to the fixtures; regenerating them is a separate,
 * deliberate step.
 *
 * Run: node mjs/regression.mjs
 */
import fs from "fs";
import path from "path";
import { fileURLToPath } from "url";
import { compile } from "../js/parser/lean.js";
import { strStmt } from "../js/parser/lean/utility.js";
import { json2regex } from "../js/parser/lean/json2regex.js";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

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

function parseStatement(lean) {
  const tree = compile(`private lemma main : ${lean} := by\n  sorry\n`);
  return findNodeByText(tree, lean);
}

/** Canonical JSON text: object keys sorted, so key order cannot fail a check. */
function canon(value) {
  if (Array.isArray(value)) return `[${value.map(canon).join(",")}]`;
  if (value && typeof value === "object") {
    const keys = Object.keys(value).sort();
    return `{${keys.map((k) => JSON.stringify(k) + ":" + canon(value[k])).join(",")}}`;
  }
  return JSON.stringify(value);
}

const show = (value) => {
  const text = typeof value === "string" ? value : canon(value);
  return text.length > 220 ? text.slice(0, 220) + "…" : text;
};

let failures = 0;
let checked = 0;
const dir = path.join(__dirname, "regression");
const files = fs.readdirSync(dir).filter((f) => f.endsWith(".json")).sort();
for (const name of files) {
  const abs = path.join(dir, name);
  let doc;
  try {
    doc = JSON.parse(fs.readFileSync(abs, "utf8"));
  } catch (e) {
    failures++;
    console.log(`FAIL ${name}\n  invalid JSON: ${e.message}`);
    continue;
  }
  if (!doc || typeof doc.lean !== "string" || typeof doc.regex !== "string" || doc.json == null) {
    console.log(`skip ${name} (not a fixture)`);
    continue;
  }
  checked++;
  const problems = [];

  // Check 2 needs no parser: the stored JSON must render to the stored regex.
  let rendered = null;
  try {
    rendered = json2regex(doc.json);
  } catch (e) {
    problems.push(`json2regex error: ${e.message}`);
  }
  if (rendered !== null && rendered !== doc.regex) {
    problems.push(`regex mismatch\n  got:  ${show(rendered)}\n  want: ${show(doc.regex)}`);
  }

  let node = null;
  let parseFailed = false;
  try {
    node = parseStatement(doc.lean);
  } catch (e) {
    parseFailed = true;
    problems.push(`parse error: ${e.message}`);
  }
  if (!node) {
    if (!parseFailed) problems.push(`no AST node matches lean:\n  ${doc.lean}`);
  } else {
    let fresh;
    try {
      fresh = node.toJSON();
    } catch (e) {
      problems.push(`toJSON error: ${e.message}`);
    }
    if (fresh !== undefined && canon(fresh) !== canon(doc.json)) {
      problems.push(`json mismatch\n  got:  ${show(fresh)}\n  want: ${show(doc.json)}`);
    }
  }

  if (problems.length) {
    failures++;
    console.log(`FAIL ${name}\n  ${problems.join("\n  ")}`);
  } else {
    console.log(`OK   ${name}`);
  }
}

console.log(`\n${failures === 0 ? "all passed" : failures + " failed"} (${checked} fixtures)`);
process.exit(failures === 0 ? 0 : 1);
