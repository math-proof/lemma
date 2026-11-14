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
  holeRegexLanguageTokens,
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
 * Columns: token | regex | consistent | suggested.
 *
 * A normal path is header + one imply row + the first `of/` stem.
 * A house `/eq/` path is header + LHS imply + RHS imply + the first `of/` stem.
 * A conjunction path (imply tokens joined by `/`, not `/eq/`) is header + one
 * row per imply token + the first `of/` stem — e.g. two identical tokens plus
 * the of-stem is three data rows.
 * `Add_Expect_Cond/eq/Expect_CondAdd` is two imply tokens, not one combined stem.
 * `All_EqProb_Cond/All_EqProb_Cond` is likewise two imply tokens (they may be identical).
 * The slash-form regex `(LHS)/eq/(RHS)` is split the same way: the LHS token is
 * matched against the LHS alternative and the RHS token against the RHS alternative.
 * A conjunction regex `A/B` (or `(A)/(B)`) is split the same way on `/`.
 * The regex column prints the stored form `(Fill)`. Matching still expands `(_|Fill)`.
 *
 * - token: imply side / first-of stem from `lemmaPath` (after Lemma/<Section>/)
 * - regex: hole-regex alternative that admits that token (consistent and suggested),
 *   otherwise the first alternative (for a house side, that side of the `/eq/` regex;
 *   for a conjunction, that side of the `/` regex)
 * - consistent: yes/no — matchImplyHoleRegex(regex, token)
 * - suggested: yes/no — token is among that alternative's token[]
 *
 * Imply may publish two optional regexes (expanded `Append(T(GetSlice__))(T(GetSlice__))`
 * and compact `AppendTSGetSlice__` / `AppendGetSliceS__`). The row shows the one that admits the path token.
 *
 * @param {string} lemmaPath
 * @param {{ from?: string, lemma?: string }} [options]
 * @returns {string}
 */
function altList(entryOrList) {
  if (!entryOrList) return [];
  if (Array.isArray(entryOrList)) return entryOrList.filter((e) => e && typeof e === "object");
  return [entryOrList];
}

/**
 * Pick the hole-regex alternative that admits `tok`.
 * Prefer consistent and suggested, then consistent, then the first alternative.
 * @param {object|object[]|null|undefined} entryOrList
 * @param {string} tok
 * @returns {{ regex: string, pad: number, consistent: boolean, suggested: boolean }}
 */
function pickMatchingAlt(entryOrList, tok, fallback) {
  const list = altList(entryOrList);
  const scored = list.map((e) => {
    const regex = String(e.regex || "_");
    const pad = e.pad;
    const consistent = !!(tok && matchImplyHoleRegex({ regex, pad }, tok));
    const toks = Array.isArray(e.token) ? e.token.map(String) : [String(e.token ?? "")];
    const suggested = !!(tok && toks.includes(String(tok)));
    return { regex, pad, consistent, suggested };
  });
  const hit =
    scored.find((s) => s.consistent && s.suggested) ||
    scored.find((s) => s.consistent) ||
    scored[0];
  if (hit) return hit;
  const regex = String(fallback?.regex || "_");
  return {
    regex,
    pad: fallback?.pad ?? 0,
    consistent: !!(tok && matchImplyHoleRegex({ regex, pad: fallback?.pad }, tok)),
    suggested: false,
  };
}

/** `Add_Expect_Cond/eq/Expect_CondAdd` → both sides; a path with no `/eq/` → null. */
function houseStemSides(stem) {
  const s = String(stem || "");
  const i = s.indexOf("/eq/");
  if (i < 0) return null;
  const lhs = s.slice(0, i);
  const rhs = s.slice(i + "/eq/".length);
  if (!lhs || !rhs || rhs.includes("/eq/")) return null;
  return { lhs, rhs };
}

/** `(LHS)/eq/(RHS)` → both alternatives. */
function houseRegexSides(regex) {
  const s = String(regex || "");
  const i = s.indexOf("/eq/");
  if (i < 0) return null;
  const lhs = s.slice(0, i);
  const rhs = s.slice(i + "/eq/".length);
  if (!lhs || !rhs) return null;
  return { lhs, rhs };
}

/**
 * Match one house side against its half of a `/eq/` regex.
 * The side's own trailing-`_` pad is used (the whole-regex pad only sees the RHS).
 * @param {string} sideRe
 * @param {string} tok
 */
function scoreHouseSide(sideRe, tok) {
  const regex = String(sideRe || "_");
  const tokens = holeRegexLanguageTokens(regex);
  const consistent = !!(tok && matchImplyHoleRegex(regex, tok));
  const suggested = !!(tok && tokens.includes(String(tok)));
  return { regex, consistent, suggested };
}

/**
 * House regex whose two sides best admit `lhs` / `rhs`.
 * @param {object[]|undefined} imply
 * @param {string} lhs
 * @param {string} rhs
 */
function pickHouseRegex(imply, lhs, rhs) {
  let best = null;
  let bestScore = -1;
  for (const e of altList(imply)) {
    const sides = houseRegexSides(e.regex);
    if (!sides) continue;
    const L = scoreHouseSide(sides.lhs, lhs);
    const R = scoreHouseSide(sides.rhs, rhs);
    const score = (L.consistent ? 2 : 0) + (R.consistent ? 2 : 0) + (L.suggested ? 1 : 0) + (R.suggested ? 1 : 0);
    if (score > bestScore) {
      bestScore = score;
      best = { L, R };
    }
  }
  return best;
}

/**
 * Split `s` on `sep` only when not inside parentheses.
 * @param {string} s
 * @param {string} sep
 * @returns {string[]}
 */
function splitTopLevel(s, sep) {
  const out = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (depth === 0 && s.startsWith(sep, i)) {
      out.push(s.slice(start, i));
      i += sep.length - 1;
      start = i + 1;
    }
  }
  out.push(s.slice(start));
  return out;
}

/** `All_EqProb_Cond/All_EqProb_Cond` → tokens; no `/`, or a `/eq/` house, → null. */
function conjStemSides(stem) {
  const s = String(stem || "");
  if (!s || s.includes("/eq/")) return null;
  const sides = splitTopLevel(s, "/").filter(Boolean);
  if (sides.length < 2) return null;
  return sides;
}

/** `AeAll_EqProbCond_Prob/AeAll_EqProbCond_Prob` or `(LHS)/(RHS)` → sides. */
function conjRegexSides(regex) {
  const s = String(regex || "");
  if (!s || s.includes("/eq/")) return null;
  const sides = splitTopLevel(s, "/");
  if (sides.length < 2 || sides.some((x) => !x)) return null;
  return sides;
}

/**
 * Conjunction regex whose sides best admit `sides`.
 * @param {object[]|undefined} imply
 * @param {string[]} sides
 */
function pickConjRegex(imply, sides) {
  let best = null;
  let bestScore = -1;
  for (const e of altList(imply)) {
    const rsides = conjRegexSides(e.regex);
    if (!rsides || rsides.length !== sides.length) continue;
    const scored = rsides.map((re, i) => scoreHouseSide(re, sides[i]));
    const score = scored.reduce((n, x) => n + (x.consistent ? 2 : 0) + (x.suggested ? 1 : 0), 0);
    if (score > bestScore) {
      bestScore = score;
      best = scored;
    }
  }
  return best;
}

/** Printed hole regex is stored `(Fill)`. `(_|Fill)` is match-time only. */
function storedRegexDisplay(regex) {
  return String(regex || "_").replace(/\(_\|/g, "(").replace(/\(_\)/g, "_");
}

function row(tok, pick) {
  const yn = (b) => (b ? "yes" : "no");
  return "| " + tok + " | " + storedRegexDisplay(pick.regex) + " | " + yn(pick.consistent) + " | " + yn(pick.suggested) + " |";
}

export function implyGivenConsistencyTable(lemmaPath, options = {}) {
  const rel = normalizeLemmaRel(lemmaPath);
  const statementAbs = resolveStatementFile(rel, options);
  const r = suggest(statementAbs, options.lemma, options);
  const implyTok = implyStemFromRelPath(rel);
  const givenTok = ofStemsFromRelPath(rel)[0] || "";
  const given0 = Array.isArray(r.givens) && r.givens[0];
  const givenPick = pickMatchingAlt(given0, givenTok, { regex: "_", pad: 0 });
  const house = houseStemSides(implyTok);
  const conj = !house && conjStemSides(implyTok);
  const lines = ["| token | regex | consistent | suggested |"];
  if (house) {
    const picked = pickHouseRegex(r.imply, house.lhs, house.rhs);
    const L = picked?.L || { regex: "_", consistent: false, suggested: false };
    const R = picked?.R || { regex: "_", consistent: false, suggested: false };
    lines.push(row(house.lhs, L));
    lines.push(row(house.rhs, R));
  } else if (conj) {
    const picked = pickConjRegex(r.imply, conj);
    for (let i = 0; i < conj.length; i++) {
      const side = picked?.[i] || { regex: "_", consistent: false, suggested: false };
      lines.push(row(conj[i], side));
    }
  } else {
    const implyPick = pickMatchingAlt(r.imply, implyTok, {
      regex: r.implyHoleRegex || "_",
      pad: holeRegexTrailingPad(r.implyHoleRegex || "_"),
    });
    lines.push(row(implyTok, implyPick));
  }
  lines.push(row(givenTok, givenPick));
  return lines.join("\n");
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
