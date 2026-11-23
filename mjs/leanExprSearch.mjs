#!/usr/bin/env node
/**
 * leanExprSearch.mjs
 * ==================
 * "Find lemmas whose conclusion has a similar structure" — the query is a Lean
 * expression instead of a keyword:
 *
 *   http://localhost/lean/?lean=a%C2%B2%2Bb%C2%B2&limit=100
 *   node mjs/leanExprSearch.mjs --search 'a ^ 2 + b ^ 2' --limit 20
 *
 * The expression is parsed with the same lean.js AST as the rest of the toolchain
 * (js/parser/lean.js, no Lean build), folded by `json2regex` / `json2plural` into
 * the structural regex vocabulary, and compared with the pre-built signature of
 * every `Lemma/**.lean` conclusion.
 *
 * Build the index once (a couple of minutes for the whole tree) and re-run it
 * whenever the lemmas change:
 *
 *   node mjs/leanExprSearch.mjs --index
 *   node mjs/leanExprSearch.mjs --index --filter Matrix/ --out /tmp/matrix-index.json
 *
 * The server reads `mjs/leanIndex.json` (built by `--index`); without it the
 * `?lean=` search reports that the index must be built first.
 */
import fs from "fs";
import os from "os";
import path from "path";
import { spawn } from "child_process";
import { fileURLToPath } from "url";
import { compile } from "../js/parser/lean.js";
import { json2regex, json2plural, json2pathPatterns } from "../js/parser/lean/json2regex.js";
import { conclusionJson } from "./lemmaPath.mjs";
import { REPO_ROOT, leanPathToModule } from "./lean/modulePath.mjs";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const LEMMA_ROOT = path.join(REPO_ROOT, "Lemma");

/** Where `--index` writes and the server reads the structural index. */
export const DEFAULT_INDEX_FILE = path.join(HERE, "leanIndex.json");

const LEMMA_DECLS = new Set(["Lean_lemma", "Lean_theorem"]);
const OPS_RE = /[A-Za-z][A-Za-z0-9]*/g;

function classOf(node) {
  return node?.constructor?.name;
}

function firstLemma(ast) {
  return (ast?.args || []).find((a) => LEMMA_DECLS.has(classOf(a))) ?? null;
}

function conclusionOfLemma(lemma) {
  const assign = (lemma?.args || []).find((a) => classOf(a) === "LeanAssign");
  const colon = (assign?.args || []).find((a) => classOf(a) === "LeanColon");
  return colon?.rhs?.toJSON?.() ?? null;
}

function uniqueRegexes(json) {
  const seen = new Set();
  const out = [];
  for (const regex of [json2regex(json), ...json2plural(json)]) {
    if (!regex || regex === "_" || seen.has(regex)) continue;
    seen.add(regex);
    out.push(regex);
  }
  return out;
}

function isRealToken(token) {
  return typeof token === "string" && token.length > 0 && token !== "_" && /^[A-Za-z0-9_]+$/.test(token);
}

/** Shortest valid path token for the whole expression, used for display. */
function bestToken(json) {
  let token = "";
  for (const { token: candidate } of json2pathPatterns(json)) {
    if (isRealToken(candidate) && (!token || candidate.length < token.length)) token = candidate;
  }
  return token;
}

/**
 * Parse a Lean expression into its structural signature.
 * @param {string} expr
 * @returns {{ json: object, regexes: string[], token: string }}
 */
export function expressionStructure(expr) {
  const source = `private lemma main : ${expr} := by\n  sorry\n`;
  let ast;
  try {
    ast = compile(source);
  } catch (e) {
    throw new Error(`Could not parse the Lean expression: ${e.message}`);
  }
  const json = conclusionOfLemma(firstLemma(ast));
  if (!json) throw new Error("Could not parse the Lean expression (no conclusion found)");
  return { json, regexes: uniqueRegexes(json), token: bestToken(json) };
}

/** Display token from the path convention: `Lemma/<section>/<token>/…/<name>.lean`. */
function tokenFromPath(rel) {
  const parts = rel.replace(/^Lemma\//, "").replace(/\.lean$/, "").split("/");
  return parts[1] ?? parts[0] ?? "";
}

function walkLeanFiles(root) {
  const out = [];
  const stack = [root];
  while (stack.length) {
    const dir = stack.pop();
    let entries;
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const entry of entries) {
      const abs = path.join(dir, entry.name);
      if (entry.isDirectory()) stack.push(abs);
      else if (entry.isFile() && entry.name.endsWith(".lean") && !entry.name.endsWith(".echo.lean")) {
        out.push(abs);
      }
    }
  }
  return out.sort();
}

/**
 * Build the structural index of every `Lemma/**.lean` conclusion.
 *
 * The lean.js parser keeps parsed ASTs alive for the whole process, so a
 * whole-tree build in one process exhausts the heap; the CLI therefore splits
 * the work over child processes (see `runIndex`). `files` lets a child process
 * index exactly the chunk it was given.
 *
 * @param {{ root?: string, filter?: string, files?: string[] }} [options]
 */
export function buildLeanIndex({ root = LEMMA_ROOT, filter = null, files = null } = {}) {
  const list = files ?? walkLeanFiles(root);
  const entries = [];
  let skipped = 0;
  for (const abs of list) {
    const rel = path.relative(REPO_ROOT, abs).split(path.sep).join("/");
    if (filter && !rel.includes(filter)) continue;
    let json;
    try {
      json = conclusionJson(abs);
    } catch {
      skipped++;
      continue;
    }
    // Base pattern only: `json2plural` (and therefore `json2pathPatterns`) can
    // blow up exponentially on a few large conclusions, which makes a
    // whole-tree build impossible. The base regex already carries the structure.
    const regex = json2regex(json);
    if (!regex || regex === "_") {
      skipped++;
      continue;
    }
    entries.push({
      module: leanPathToModule(rel),
      path: rel,
      token: tokenFromPath(rel),
      regexes: [regex],
    });
  }
  return {
    generatedAt: new Date().toISOString(),
    root: path.relative(REPO_ROOT, root).split(path.sep).join("/"),
    skipped,
    entries,
  };
}

/** Loaded once per process; the server reads the JSON written by `--index`. */
let memoryIndex = null;

export function loadLeanIndex(file = DEFAULT_INDEX_FILE) {
  if (memoryIndex) return memoryIndex;
  if (file && fs.existsSync(file)) {
    memoryIndex = JSON.parse(fs.readFileSync(file, "utf8"));
    return memoryIndex;
  }
  throw new Error(
    `no structural index at ${file}; run: node mjs/leanExprSearch.mjs --index`,
  );
}

function opsOf(regex, memo) {
  const cached = memo.get(regex);
  if (cached) return cached;
  const ops = regex.match(OPS_RE) ?? [];
  memo.set(regex, ops);
  return ops;
}

function countMap(seq) {
  const map = new Map();
  for (const x of seq) map.set(x, (map.get(x) ?? 0) + 1);
  return map;
}

function jaccard(a, b) {
  if (a.length === 0 && b.length === 0) return 0;
  const ma = countMap(a);
  const mb = countMap(b);
  let inter = 0;
  let union = 0;
  for (const [k, v] of ma) {
    union += v;
    const w = mb.get(k);
    if (w) inter += Math.min(v, w);
  }
  for (const [k, v] of mb) if (!ma.has(k)) union += v;
  return union === 0 ? 0 : inter / union;
}

function bigrams(seq) {
  const out = [];
  for (let i = 0; i + 1 < seq.length; i++) out.push(`${seq[i]} ${seq[i + 1]}`);
  return out;
}

/** Structural similarity of two signature regexes, in [0, 1]. */
export function regexSimilarity(queryRegex, lemmaRegex, memo = new Map()) {
  if (queryRegex === lemmaRegex) return 1;
  const q = opsOf(queryRegex, memo);
  const l = opsOf(lemmaRegex, memo);
  if (q.length === 0 || l.length === 0) return 0;
  const ops = jaccard(q, l);
  const pairs = jaccard(bigrams(q), bigrams(l));
  const head = q[0] === l[0] ? 1 : 0;
  // No shared operator at all: unrelated skeletons, not a weak match.
  if (ops === 0 && pairs === 0 && head === 0) return 0;
  const size = Math.min(q.length, l.length) / Math.max(q.length, l.length);
  return 0.5 * ops + 0.25 * pairs + 0.15 * head + 0.1 * size;
}

/**
 * Search the most similar lemma conclusions.
 * @param {string} expr - a Lean expression, e.g. `a ^ 2 + b ^ 2`.
 * @param {{ limit?: number, index?: object, indexFile?: string }} [options]
 * @returns {{ module: string, path: string, token: string, score: number, regex: string }[]}
 */
export function searchLeanExpression(expr, { limit = 20, index = null, indexFile = DEFAULT_INDEX_FILE } = {}) {
  const query = expressionStructure(expr);
  const data = index ?? loadLeanIndex(indexFile);
  const memo = new Map();
  const hits = [];
  for (const entry of data.entries) {
    let best = 0;
    let bestRegex = "";
    for (const qr of query.regexes) {
      for (const lr of entry.regexes) {
        const score = regexSimilarity(qr, lr, memo);
        if (score > best) {
          best = score;
          bestRegex = lr;
        }
        if (best === 1) break;
      }
      if (best === 1) break;
    }
    if (best > 0) {
      hits.push({
        module: entry.module,
        path: entry.path,
        token: entry.token,
        score: Number(best.toFixed(4)),
        regex: bestRegex,
      });
    }
  }
  hits.sort((a, b) => b.score - a.score || a.path.length - b.path.length);
  return { query, hits: hits.slice(0, Math.max(1, limit)) };
}

function usage() {
  console.error(`usage: node mjs/leanExprSearch.mjs [options]

  --index              build the structural index and write it (see --out)
  --out <file>         index output path (default: mjs/leanIndex.json)
  --filter <str>       only index paths containing <str>   (e.g. Matrix/)
  --chunk-size <n>     files per child process (default: 250, 0 = single process)
  --search <lean>      search lemmas similar to a Lean expression
  --limit <n>          max results (default: 20)
  --json               print the search result as JSON
  -h, --help           this message`);
}

function parseArgs(argv) {
  const opts = {
    mode: null,
    out: DEFAULT_INDEX_FILE,
    filter: null,
    search: null,
    limit: 20,
    json: false,
    chunkSize: 250,
    filesFrom: null,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--index") opts.mode = "index";
    else if (a === "--out") opts.out = argv[++i] ?? DEFAULT_INDEX_FILE;
    else if (a === "--filter") opts.filter = argv[++i] ?? "";
    else if (a === "--chunk-size") opts.chunkSize = Number(argv[++i]) || 0;
    else if (a === "--files-from") opts.filesFrom = argv[++i] ?? null;
    else if (a === "--search") {
      opts.mode = "search";
      opts.search = argv[++i] ?? "";
    } else if (a === "--limit") opts.limit = Number(argv[++i]) || 20;
    else if (a === "--json") opts.json = true;
    else if (a === "-h" || a === "--help") opts.mode = "help";
    else if (a.startsWith("-")) throw new Error(`unknown option: ${a}`);
    else {
      opts.mode = "search";
      opts.search = a;
    }
  }
  return opts;
}

/**
 * Build the index, splitting the tree over child processes.
 *
 * A single process cannot parse the whole tree: lean.js retains each AST and the
 * heap grows past several GB after a few thousand files. Small chunks keep every
 * child small; a few run in parallel and their results are merged.
 */
async function runIndex(opts) {
  const t0 = performance.now();
  let files = null;
  if (!opts.filesFrom) {
    files = walkLeanFiles(LEMMA_ROOT);
    if (opts.filter) {
      files = files.filter((f) => path.relative(REPO_ROOT, f).split(path.sep).join("/").includes(opts.filter));
    }
  }
  let index;
  if (files && files.length > opts.chunkSize && opts.chunkSize > 0) {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "lean-index-"));
    const self = fileURLToPath(import.meta.url);
    const chunks = Math.ceil(files.length / opts.chunkSize);
    const entries = [];
    let skipped = 0;
    let done = 0;
    let next = 0;
    const runChunk = (c) => {
      const listFile = path.join(tmp, `files-${c}.txt`);
      const partFile = path.join(tmp, `part-${c}.json`);
      fs.writeFileSync(listFile, files.slice(c * opts.chunkSize, (c + 1) * opts.chunkSize).join("\n"));
      return new Promise((resolve, reject) => {
        const child = spawn(
          process.execPath,
          [self, "--index", "--files-from", listFile, "--out", partFile, "--chunk-size", "0"],
          { stdio: ["ignore", "ignore", "inherit"] },
        );
        child.on("error", reject);
        child.on("close", (code) => {
          if (code !== 0) return reject(new Error(`index chunk ${c + 1}/${chunks} failed (${code})`));
          const part = JSON.parse(fs.readFileSync(partFile, "utf8"));
          entries.push(...part.entries);
          skipped += part.skipped;
          done++;
          console.error(`  chunk ${done}/${chunks}: ${part.entries.length} conclusions`);
          resolve();
        });
      });
    };
    const workers = Math.max(1, Math.min(4, (os.cpus()?.length ?? 2) - 1));
    await Promise.all(
      Array.from({ length: workers }, async () => {
        while (next < chunks) await runChunk(next++);
      }),
    );
    index = { generatedAt: new Date().toISOString(), root: "Lemma", skipped, entries };
  } else {
    index = buildLeanIndex({
      filter: opts.filesFrom ? null : opts.filter,
      files: opts.filesFrom ? fs.readFileSync(opts.filesFrom, "utf8").split("\n").filter(Boolean) : null,
    });
  }
  fs.writeFileSync(opts.out, JSON.stringify(index));
  memoryIndex = index;
  console.log(
    `indexed ${index.entries.length} conclusions (${index.skipped} skipped) in ` +
      `${((performance.now() - t0) / 1000).toFixed(1)}s -> ${path.relative(process.cwd(), opts.out)}`,
  );
}

async function main() {
  let opts;
  try {
    opts = parseArgs(process.argv.slice(2));
  } catch (e) {
    console.error(e.message);
    usage();
    process.exitCode = 2;
    return;
  }
  if (opts.mode === "help" || !opts.mode) {
    usage();
    return;
  }
  if (opts.mode === "index") {
    await runIndex(opts);
    return;
  }
  const { query, hits } = searchLeanExpression(opts.search, { limit: opts.limit });
  if (opts.json) {
    console.log(JSON.stringify({ query: opts.search, structure: query.regexes[0], token: query.token, hits }, null, 2));
    return;
  }
  console.log(`structure: ${query.regexes[0]}`);
  if (hits.length === 0) {
    console.log("no similar lemma found");
    return;
  }
  console.log("");
  console.log("| score | module | regex |");
  console.log("| --- | --- | --- |");
  for (const hit of hits) console.log(`| ${hit.score.toFixed(3)} | ${hit.module} | ${hit.regex} |`);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((e) => {
    console.error(e.message);
    process.exitCode = 1;
  });
}
