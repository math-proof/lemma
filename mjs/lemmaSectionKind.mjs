#!/usr/bin/env node
/**
 * lemmaSectionKind.mjs
 * ====================
 * Classify each top-level `Lemma/<Section>/` folder as:
 *   - data type     (Mathlib structure / inductive / type-forming def)
 *   - type class    (`Lean.isClass`)
 *   - topic/unknown (missing in Mathlib, or not a type)
 *
 * Uses one `lake env lean` pass (same pattern as `mjs/lean/mathlibRequest.mjs`)
 * that loads Mathlib and inspects the environment.
 *
 *   node mjs/lemmaSectionKind.mjs
 *   node mjs/lemmaSectionKind.mjs Algebra Analysis AdicCompletion Int
 *   node mjs/lemmaSectionKind.mjs --json
 *   node mjs/lemmaSectionKind.mjs --json out.json Algebra Real
 *
 * Exit code: 0 on success, 1 on Lean/spawn failure.
 */
import fs from 'fs';
import os from 'os';
import path from 'path';
import { fileURLToPath } from 'url';
import { REPO_ROOT } from './lean/modulePath.mjs';
import { listLemmaTopLevelDirs } from './lean/lemmaSections.mjs';
import { get_lake_path, get_lean_env, spawnLakeLean } from './lean/echo2vue.mjs';

/** Lean checker body; `{{LEAVES}}` is replaced with `#["A", "B", …]`. */
const LEAN_CHECKER = `import Mathlib
open Lean Meta

/-- Candidates whose last name component equals \`leaf\`. -/
def candidates (env : Environment) (leaf : String) : Array Name :=
  let exact := Name.mkSimple leaf
  if (env.find? exact).isSome then
    #[exact]
  else
    env.constants.fold (init := (#[] : Array Name)) fun acc n _info =>
      if !n.isStr then acc
      else if n.getString! != leaf then acc
      else if n.toString.contains "_private" || n.toString.contains "_@" then acc
      else acc.push n

/-- Higher is better. Prefer type classes / structures / type-forming defs. -/
def scoreCandidate (env : Environment) (n : Name) : MetaM Nat := do
  let lengthPenalty := n.toString.length
  if isClass env n then return 100000 - lengthPenalty
  if isStructure env n then return 100000 - lengthPenalty
  match env.find? n with
  | some (.inductInfo _) =>
    return 100000 - lengthPenalty
  | some (.defnInfo info) => do
    let isType ← try Meta.isTypeFormerType info.type catch _ => pure false
    if isType then return 90000 - lengthPenalty else return 10000 - lengthPenalty
  | some (.thmInfo _) => return 1000 - lengthPenalty
  | _ => return 100 - lengthPenalty

def resolveName (env : Environment) (leaf : String) : MetaM (Option Name) := do
  let cs := candidates env leaf
  if cs.isEmpty then return none
  let mut best : Option (Name × Nat) := none
  for n in cs do
    let s ← scoreCandidate env n
    match best with
    | none => best := some (n, s)
    | some (_, bs) =>
      if s > bs then best := some (n, s)
  return best.map (·.1)

def declKind (env : Environment) (n : Name) : MetaM String := do
  if isClass env n then
    return "typeclass"
  if isStructure env n then
    return "structure"
  match env.find? n with
  | some (.inductInfo _) =>
    return "inductive"
  | some (.defnInfo info) => do
    let isType ← try Meta.isTypeFormerType info.type catch _ => pure false
    if isType then return "def-type" else return "def"
  | some (.thmInfo _) => return "theorem"
  | some (.axiomInfo _) => return "axiom"
  | some (.opaqueInfo _) => return "opaque"
  | some (.quotInfo _) => return "quot"
  | some (.ctorInfo _) => return "constructor"
  | some (.recInfo _) => return "recursor"
  | none => return "missing"

def classifyOne (leaf : String) : MetaM Json := do
  let env ← getEnv
  match ← resolveName env leaf with
  | none =>
    return Json.mkObj [
      ("folder", Json.str leaf),
      ("resolved", Json.null),
      ("decl", Json.str "missing"),
      ("kind", Json.str "topic/unknown"),
      ("reason", Json.str "no Mathlib constant whose last name component equals this folder")
    ]
  | some n => do
    let decl ← declKind env n
    let (kind, reason) : String × String :=
      match decl with
      | "typeclass" => ("type class", s!"Mathlib \`{n}\` is a type class (\`Lean.isClass\`)")
      | "structure" => ("data type", s!"Mathlib \`{n}\` is a structure")
      | "inductive" => ("data type", s!"Mathlib \`{n}\` is an inductive (not a class)")
      | "def-type"  => ("data type", s!"Mathlib \`{n}\` is a def of a type former")
      | "def"       => ("topic/unknown", s!"Mathlib \`{n}\` is a def, but not a type former")
      | "theorem"   => ("topic/unknown", s!"Mathlib \`{n}\` is a theorem, not a type")
      | other       => ("topic/unknown", s!"Mathlib \`{n}\` has decl kind \`{other}\`")
    return Json.mkObj [
      ("folder", Json.str leaf),
      ("resolved", Json.str (toString n)),
      ("decl", Json.str decl),
      ("kind", Json.str kind),
      ("reason", Json.str reason)
    ]

#eval show MetaM Unit from do
  let leaves : Array String := {{LEAVES}}
  let mut arr : Array Json := #[]
  for leaf in leaves do
    arr := arr.push (← classifyOne leaf)
  IO.println (toString (Json.arr arr))
`;

function usage() {
  console.error(`usage: node mjs/lemmaSectionKind.mjs [options] [Folder ...]

Classify Lemma/ top-level section folders via Mathlib (Lean.isClass / isStructure / type formers).

  (no folders)     classify every top-level directory under Lemma/
  Folder ...       classify only these names (need not exist on disk)

Options:
  --json [file]    print JSON (to stdout, or write file if path given)
  -h, --help       this message`);
}

/**
 * @param {string[]} argv
 */
function parseArgs(argv) {
  /** @type {{ folders: string[]; json: boolean | string; help: boolean }} */
  const opts = { folders: [], json: false, help: false };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '-h' || a === '--help') opts.help = true;
    else if (a === '--json') {
      const next = argv[i + 1];
      // Path if it looks like a file (has . / \); otherwise bare --json → stdout.
      if (next && !next.startsWith('-') && /[./\\]/.test(next)) {
        opts.json = argv[++i];
      } else {
        opts.json = true;
      }
    } else if (a.startsWith('-')) {
      throw new Error(`unknown option: ${a}`);
    } else {
      opts.folders.push(a);
    }
  }
  return opts;
}

/** Escape a folder name for a Lean string literal. */
function leanStringLiteral(s) {
  return `"${String(s).replace(/\\/g, '\\\\').replace(/"/g, '\\"')}"`;
}

/**
 * @param {string} text
 * @returns {unknown[] | null}
 */
function extractJsonArray(text) {
  if (!text || typeof text !== 'string') return null;
  const tryParse = (t) => {
    try {
      const v = JSON.parse(t);
      return Array.isArray(v) ? v : null;
    } catch {
      return null;
    }
  };
  const trimmed = text.trim();
  let a = tryParse(trimmed);
  if (a) return a;
  // Prefer the last JSON array in the output (after lake notes / warnings).
  const start = text.lastIndexOf('[');
  if (start < 0) return null;
  let depth = 0;
  for (let i = start; i < text.length; i++) {
    const c = text[i];
    if (c === '[') depth++;
    else if (c === ']') {
      depth--;
      if (depth === 0) {
        a = tryParse(text.slice(start, i + 1));
        if (a) return a;
        break;
      }
    }
  }
  return null;
}

/**
 * @param {Array<Record<string, unknown>>} rows
 */
function printTable(rows) {
  const cols = [
    { key: 'folder', title: 'folder' },
    { key: 'kind', title: 'kind' },
    { key: 'resolved', title: 'resolved' },
    { key: 'decl', title: 'decl' },
    { key: 'reason', title: 'reason' },
  ];
  /** @type {Record<string, number>} */
  const widths = {};
  for (const c of cols) {
    widths[c.key] = c.title.length;
    for (const r of rows) {
      const v = r[c.key] == null ? '-' : String(r[c.key]);
      widths[c.key] = Math.max(widths[c.key], v.length);
    }
  }
  const line = (/** @type {Record<string, unknown>} */ r) =>
    cols
      .map((c) => {
        const v = r[c.key] == null ? '-' : String(r[c.key]);
        return v.padEnd(widths[c.key]);
      })
      .join('  ');
  console.log(line(Object.fromEntries(cols.map((c) => [c.key, c.title]))));
  console.log(cols.map((c) => '-'.repeat(widths[c.key])).join('  '));
  for (const r of rows) console.log(line(r));
}

/**
 * @param {string[]} folders
 * @returns {Promise<Array<Record<string, unknown>>>}
 */
export async function classifyLemmaSections(folders) {
  if (!folders.length) {
    throw new Error('no folders to classify');
  }
  const leavesLit = `#[${folders.map(leanStringLiteral).join(', ')}]`;
  const leanSrc = LEAN_CHECKER.replace('{{LEAVES}}', leavesLit);
  const tmpLean = path.join(os.tmpdir(), `lemmaSectionKind-${process.pid}-${Date.now()}.lean`);
  await fs.promises.writeFile(tmpLean, leanSrc, 'utf8');
  try {
    const lakePath = get_lake_path();
    const env = {
      ...get_lean_env(REPO_ROOT),
      ELAN_NO_OVERRIDE_NOTICE: '1',
      PATH: `${path.dirname(lakePath)}${path.delimiter}${process.env.PATH || ''}`,
    };
    const r = await spawnLakeLean(lakePath, ['env', 'lean', tmpLean], {
      cwd: REPO_ROOT,
      env,
      windowsHide: true,
    });
    if (r.error) {
      throw new Error(`lean spawn failed: ${r.error.message}\n${(r.stderr || '').slice(0, 4000)}`);
    }
    const outText = `${r.stdout || ''}\n${r.stderr || ''}`;
    const arr = extractJsonArray(outText);
    if (!arr) {
      throw new Error(`no JSON array in Lean output:\n${outText.slice(0, 8000)}`);
    }
    return /** @type {Array<Record<string, unknown>>} */ (arr);
  } finally {
    try {
      await fs.promises.unlink(tmpLean);
    } catch {
      /* ignore */
    }
  }
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  if (opts.help) {
    usage();
    process.exit(0);
  }
  const folders =
    opts.folders.length > 0
      ? opts.folders
      : listLemmaTopLevelDirs().sort((a, b) => a.localeCompare(b, undefined, { sensitivity: 'base' }));
  if (!folders.length) {
    console.error('no Lemma/ folders found and no names given');
    process.exit(1);
  }
  const rows = await classifyLemmaSections(folders);
  // Stable order: CLI order if given, else alphabetical (already sorted).
  if (opts.json === true) {
    console.log(JSON.stringify(rows, null, 2));
  } else if (typeof opts.json === 'string') {
    const outPath = path.isAbsolute(opts.json) ? opts.json : path.join(process.cwd(), opts.json);
    await fs.promises.writeFile(outPath, JSON.stringify(rows, null, 2) + '\n', 'utf8');
    console.error(`wrote ${outPath}`);
    printTable(rows);
  } else {
    printTable(rows);
  }
}

const isMain =
  process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url));

if (isMain) {
  main().catch((e) => {
    console.error(e?.stack || e);
    process.exit(1);
  });
}
