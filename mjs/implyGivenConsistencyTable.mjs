/**
 * Imply/given consistency markdown table for a Lemma path.
 *
 * Uses lemmaPath.suggest() for hole-regex + suggested token[], and the path
 * itself for the imply / first-of stems. When the candidate path is missing on
 * disk, loads the Lean statement from --from / options.from, or from a
 * same-section live leaf that shares the `/of/…` tail.
 *
 * CLI:
 *   node mjs/implyGivenConsistencyTable.mjs [--from <statement.lean>] <Lemma/.../.lean>
 * Also: node mjs/lemmaPath.mjs --table [--from <statement.lean>] <Lemma/.../.lean>
 */
import fs from "fs";
import path from "path";
import { fileURLToPath, pathToFileURL } from "url";
import {
  suggest,
  matchImplyHoleRegex,
  implyStemFromRelPath,
  ofStemsFromRelPath,
  holeRegexTrailingPad,
} from "./lemmaPath.mjs";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const LEMMA_ROOT = path.join(REPO, "Lemma");

/** Normalize a Lemma path to `Section/.../.lean` (no `Lemma/` prefix). */
function normalizeLemmaRel(lemmaPath) {
  let s = String(lemmaPath || "").replace(/\\/g, "/");
  if (s.startsWith("Lemma/")) s = s.slice("Lemma/".length);
  if (!s.endsWith(".lean")) s += ".lean";
  return s;
}

/**
 * Resolve the on-disk Lean file whose *statement* feeds suggest() for a table.
 * Tokens always come from `lemmaPath`; the statement may come from elsewhere when
 * the candidate path is not on disk yet (rename / CoeGet-style proposals).
 *
 * Order: options.from → existing lemmaPath → same-section leaf with the same `/of/…` tail.
 * @param {string} lemmaPath
 * @param {{ from?: string }} [options]
 * @returns {string} absolute path
 */
export function resolveStatementFile(lemmaPath, options = {}) {
  if (options.from) {
    const from = path.resolve(String(options.from));
    if (!fs.existsSync(from)) throw new Error("statement --from not found: " + from);
    return from;
  }
  const rel = normalizeLemmaRel(lemmaPath);
  const abs = path.join(LEMMA_ROOT, rel);
  if (fs.existsSync(abs)) return abs;
  const ofSegs = ofStemsFromRelPath(rel);
  const section = rel.split("/").filter(Boolean)[0];
  if (!section || !ofSegs.length) {
    throw new Error("lemma path missing on disk and no /of/ tail to locate a statement: Lemma/" + rel);
  }
  const ofTail = ofSegs.join("/") + ".lean";
  const sectionRoot = path.join(LEMMA_ROOT, section);
  if (!fs.existsSync(sectionRoot)) {
    throw new Error("lemma path missing and section not found: Lemma/" + section);
  }
  const found = [];
  const walk = (dir) => {
    let ents;
    try { ents = fs.readdirSync(dir, { withFileTypes: true }); } catch { return; }
    for (const ent of ents) {
      const p = path.join(dir, ent.name);
      if (ent.isDirectory()) walk(p);
      else if (ent.isFile() && ent.name.endsWith(".lean") && !ent.name.endsWith(".echo.lean")) {
        const relP = path.relative(LEMMA_ROOT, p).replace(/\\/g, "/");
        if (relP.endsWith("/of/" + ofTail)) found.push(p);
      }
    }
  };
  walk(sectionRoot);
  if (!found.length) {
    throw new Error(
      "lemma path missing on disk; no live Lemma/" + section + "/…/of/" + ofTail +
      " to load a statement from (pass options.from / --from)"
    );
  }
  found.sort((a, b) => a.length - b.length || (a < b ? -1 : a > b ? 1 : 0));
  return found[0];
}

/**
 * Markdown table: path imply/given stems vs hole-regex + suggested token[].
 * Exact shape — 3 rows (header + imply + given), 4 columns:
 *   token | regex | consistent | suggested
 *
 * - token: imply / first-of stem from `lemmaPath` (after Lemma/<Section>/)
 * - regex: primary implyHoleRegex / first given hole regex from suggest(statement)
 * - consistent: yes/no — matchImplyHoleRegex(regex, token)
 * - suggested: yes/no — token is among that role's primary token[]
 *
 * @param {string} lemmaPath
 * @param {{ from?: string, lemma?: string }} [options]
 * @returns {string}
 */
export function implyGivenConsistencyTable(lemmaPath, options = {}) {
  const rel = normalizeLemmaRel(lemmaPath);
  const statementAbs = resolveStatementFile(rel, options);
  const r = suggest(statementAbs, options.lemma, options);
  const implyTok = implyStemFromRelPath(rel);
  const givenTok = ofStemsFromRelPath(rel)[0] || "";
  const implyEntry = (Array.isArray(r.imply) && r.imply[0]) || {
    token: [],
    regex: r.implyHoleRegex || "_",
    pad: holeRegexTrailingPad(r.implyHoleRegex || "_"),
  };
  const given0 = Array.isArray(r.givens) && r.givens[0];
  const givenEntry = (Array.isArray(given0) ? given0[0] : given0) || {
    token: [],
    regex: "_",
    pad: 0,
  };
  const implyRe = String(implyEntry.regex || "_");
  const givenRe = String(givenEntry.regex || "_");
  const yn = (b) => (b ? "yes" : "no");
  const implyConsistent = !!(implyTok && matchImplyHoleRegex({ regex: implyRe, pad: implyEntry.pad }, implyTok));
  const givenConsistent = !!(givenTok && matchImplyHoleRegex({ regex: givenRe, pad: givenEntry.pad }, givenTok));
  const implyToks = Array.isArray(implyEntry.token) ? implyEntry.token : [implyEntry.token];
  const givenToks = Array.isArray(givenEntry.token) ? givenEntry.token : [givenEntry.token];
  const implySuggested = implyToks.map(String).includes(implyTok);
  const givenSuggested = givenToks.map(String).includes(givenTok);
  return [
    "| token | regex | consistent | suggested |",
    "| " + implyTok + " | " + implyRe + " | " + yn(implyConsistent) + " | " + yn(implySuggested) + " |",
    "| " + givenTok + " | " + givenRe + " | " + yn(givenConsistent) + " | " + yn(givenSuggested) + " |",
  ].join("\n");
}

function cli() {
  const argv = process.argv.slice(2);
  const fromIdx = argv.indexOf("--from");
  const fromPath = fromIdx >= 0 ? argv[fromIdx + 1] : null;
  const lemmaIdx = argv.indexOf("--lemma");
  const lemmaName = lemmaIdx >= 0 ? argv[lemmaIdx + 1] : null;
  const reserved = new Set([fromPath, lemmaName].filter(Boolean));
  const file = argv.find((a) => !a.startsWith("-") && !reserved.has(a));
  if (!file) {
    console.error("Usage: node mjs/implyGivenConsistencyTable.mjs [--from <statement.lean>] [--lemma <name>] <Lemma/.../.lean>");
    process.exit(1);
  }
  try {
    console.log(implyGivenConsistencyTable(file, { from: fromPath || undefined, lemma: lemmaName || undefined }));
  } catch (e) {
    console.error(e.message || e);
    process.exit(1);
  }
}

const isMain =
  process.argv[1] &&
  pathToFileURL(path.resolve(process.argv[1])).href === import.meta.url;
if (isMain) cli();
