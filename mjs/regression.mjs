/**
 * regression.mjs — JSON / hole-regex regression over `mjs/regression/*.json`.
 *
 * Fixtures can use parallel `regex`, `suggestion`, and `dag` arrays, stored in
 * canonical order: shortest regex first, so the base is not necessarily index 0.
 * Legacy fixtures store the base and plural values in separate fields.
 *
 * Read-only checks per fixture:
 *   1. `json`  — parse `lean`, locate the statement node, and require its
 *      `toJSON({ leaves: new Map(), binders: [] })` to deep-equal the stored
 *      `json` field (key order ignored). This is the fingerprint tree, with
 *      free leaves as `$n` and binders as De Bruijn `?n`.
 *   2. `regex` — require `json2regex(stored json)` to equal `regex`.
 *   3. `plural`— require `json2plural(stored json)` to equal `plural`
 *      (as a set; order is not significant).
 *   3b. `order` — indexed fixtures must store `regex` and `suggestion` in
 *      `json2pathPatterns` order, which decides the emitted path.
 *   4. `suggestion` — match the stored path against `regex`.
 *   5. `pluralSuggestion` — match each stored path against its paired `plural`
 *      regex in fixture order.
 *   6. `dag` — check each indexed graph and compare the base DAG from JSON
 *      with the base DAG from the regex string.
 *   7. `fingerprint` — require the infix rendering of `toJSON` to equal the
 *      stored field. Free leaves are named by first appearance, so `√a + a²`
 *      is `√$1 + $1²` while `√a + b²` is `√$1 + $2²`. Bound variables of sums, products, and
 *      quantifiers are De Bruijn `?0`, `?1`, … (`?0` is nearest); `ℙ[π]`,
 *      `∇[x]`, and `∂[x]` do not bind, but `∇[x = x₀]` and `∂[x = x₀]` do.
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
import { dag2suggession, json2dag, json2regex, json2plural, json2pathPatterns, regex2dag, suggestionMatches } from "../js/parser/lean/json2regex.js";
import { infixFingerprint } from "./lean/infixFingerprint.mjs";

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
  // The canonical order is shortest-first, so the base regex need not sit at index 0.
  if (rendered !== null && !regexes.includes(rendered)) {
    problems.push(`base regex missing\n  got:  ${show(regexes)}\n  want: ${show(rendered)}`);
  }

  // Check 3: S-plural variants, compared as a set (order is not significant).
  let plurals = null;
  try {
    plurals = [...new Set(json2plural(doc.json))].sort();
  } catch (e) {
    problems.push(`json2plural error: ${e.message}`);
  }
  if (plurals !== null) {
    const want = [...new Set(regexes.filter((regex) => regex !== rendered))].sort();
    if (JSON.stringify(plurals) !== JSON.stringify(want)) {
      problems.push(`plural mismatch\n  got:  ${show(plurals)}\n  want: ${show(want)}`);
    }
  }

  // Check 3b: the canonical order is shortest regex first, and the emitted path is
  // taken from the front of that list, so both arrays must be stored in that exact
  // order. A reordering is a behaviour change, not a cosmetic diff.
  if (indexed) {
    try {
      const patterns = json2pathPatterns(doc.json);
      const wantRegex = patterns.map(({ regex }) => regex);
      const wantSuggestion = patterns.map(({ token }) => token);
      if (JSON.stringify(regexes) !== JSON.stringify(wantRegex)) {
        problems.push(`regex order mismatch\n  got:  ${show(regexes)}\n  want: ${show(wantRegex)}`);
      }
      if (JSON.stringify(suggestions) !== JSON.stringify(wantSuggestion)) {
        problems.push(`suggestion order mismatch\n  got:  ${show(suggestions)}\n  want: ${show(wantSuggestion)}`);
      }
    } catch (e) {
      problems.push(`json2pathPatterns error: ${e.message}`);
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
          const isBase = regex === rendered;
          const graph = isBase ? json2dag(doc.json) : regex2dag(regex);
          if (canon(doc.dag[i]) !== canon(graph)) problems.push(`dag[${i}] mismatch`);
          if (isBase && canon(graph) !== canon(regex2dag(regex))) {
            problems.push(`dag[${i}] differs between the JSON node and the regex string`);
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
      fresh = node.toJSON({ leaves: new Map(), binders: [] });
    } catch (e) {
      problems.push(`toJSON error: ${e.message}`);
    }
    if (fresh !== undefined && canon(fresh) !== canon(doc.json)) {
      problems.push(`json mismatch\n  got:  ${show(fresh)}\n  want: ${show(doc.json)}`);
    }

    // Check 7: leaf-identity fingerprint, printed infix. `toJSON` names a leaf
    // on its first appearance, so `√a + a²` shares `$1` while `√a + b²` gets `$1`/`$2`.
    if (typeof doc.fingerprint !== "string" || doc.fingerprint === "") {
      problems.push("fingerprint is missing");
    } else {
      let fingerprint = null;
      try {
        fingerprint = infixFingerprint(node.toJSON({ leaves: new Map(), binders: [] }));
      } catch (e) {
        problems.push(`fingerprint error: ${e.message}`);
      }
      if (fingerprint != null && fingerprint !== doc.fingerprint) {
        problems.push(`fingerprint mismatch\n  got:  ${show(fingerprint)}\n  want: ${show(doc.fingerprint)}`);
      }
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
