/**
 * regression.mjs — JSON / hole-regex regression over `mjs/regression/*.json`.
 *
 * Fixtures can use parallel `regex`, `suggestion`, and `dag` arrays.
 * Index 0 is the base pattern and subsequent indices are plural variants.
 * Legacy fixtures store the base and plural values in separate fields.
 *
 * Read-only checks per fixture:
 *   1. `json`  — parse `lean`, locate the statement node, and require its
 *      `toJSON()` to deep-equal the stored `json` field (key order ignored).
 *   2. `regex` — require `json2regex(stored json)` to equal `regex`.
 *   3. `plural`— require `json2plural(stored json)` to equal `plural`
 *      (as a set; order is not significant).
 *   4. `suggestion` — match the stored path against `regex`.
 *   5. `pluralSuggestion` — match each stored path against its paired `plural`
 *      regex in fixture order.
 *   6. `dag` — check each indexed graph and compare the base DAG from JSON
 *      with the base DAG from the regex string.
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
import { dag2suggession, json2dag, json2regex, json2plural, regex2dag, suggestionMatches } from "../js/parser/lean/json2regex.js";

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
  return text?.length > 220 ? text.slice(0, 220) + "…" : text;
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
  if (!doc || typeof doc.lean !== "string" || doc.json == null) {
    console.log(`skip ${name} (not a fixture)`);
    continue;
  }
  checked++;
  const problems = [];
  const indexed = Array.isArray(doc.regex);
  const regexes = indexed ? doc.regex : [doc.regex, ...(Array.isArray(doc.plural) ? doc.plural : [])];
  const suggestions = indexed ? doc.suggestion :
    [doc.suggestion, ...(Array.isArray(doc.pluralSuggestion) ? doc.pluralSuggestion : [])];
  const [baseRegex, ...wantPlural] = regexes;
  if (!regexes.length || !regexes.every((regex) => typeof regex === "string") ||
      (!indexed && !Array.isArray(doc.plural))) {
    problems.push("expected a base regex and an array of plural regex strings");
  }

  // Check 2 needs no parser: the stored JSON must render to the stored regex.
  let rendered = null;
  try {
    rendered = json2regex(doc.json);
  } catch (e) {
    problems.push(`json2regex error: ${e.message}`);
  }
  if (rendered !== null && rendered !== baseRegex) {
    problems.push(`regex mismatch\n  got:  ${show(rendered)}\n  want: ${show(baseRegex)}`);
  }

  // Check 3: S-plural variants, compared as a set (order is not significant).
  let plurals = null;
  try {
    plurals = [...new Set(json2plural(doc.json))].sort();
  } catch (e) {
    problems.push(`json2plural error: ${e.message}`);
  }
  if (plurals !== null) {
    const want = [...new Set(wantPlural)].sort();
    if (JSON.stringify(plurals) !== JSON.stringify(want)) {
      problems.push(`plural mismatch\n  got:  ${show(plurals)}\n  want: ${show(want)}`);
    }
  }

  if (!Array.isArray(suggestions) || suggestions.length !== regexes.length ||
      (!indexed && !Array.isArray(doc.pluralSuggestion))) {
    problems.push(`expected one suggestion for each of the ${regexes.length} regexes`);
  } else {
    regexes.forEach((regex, i) => {
      const suggestion = suggestions[i];
      if (!suggestionMatches(regex, suggestion)) {
        problems.push(`suggestion[${i}] mismatch\n  path:  ${show(suggestion)}\n  regex: ${show(regex)}`);
      }
    });
  }

  if (indexed) {
    if (!Array.isArray(doc.dag) || doc.dag.length !== regexes.length) {
      problems.push(`dag must contain one graph for each of the ${regexes.length} regexes`);
    } else {
      regexes.forEach((regex, i) => {
        if (typeof regex !== "string") return;
        try {
          const graph = i === 0 ? json2dag(doc.json) : regex2dag(regex);
          if (canon(doc.dag[i]) !== canon(graph)) problems.push(`dag[${i}] mismatch`);
          if (i === 0 && canon(graph) !== canon(regex2dag(regex))) {
            problems.push("dag[0] differs between the JSON node and the regex string");
          }
          if (!suggestionMatches(regex, dag2suggession(graph))) {
            problems.push(`dag[${i}] did not generate a matching suggestion`);
          }
        } catch (e) {
          problems.push(`dag[${i}] error: ${e.message}`);
        }
      });
    }
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
