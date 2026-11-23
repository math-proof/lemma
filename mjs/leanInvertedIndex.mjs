#!/usr/bin/env node
/**
 * leanInvertedIndex.mjs
 * =====================
 * Build the inverted index of lemma-conclusion operator heads and upload it
 * to axiom.inverted (`name`, `id`, `count`), whose `id` is axiom.lemma.id.
 * Each document's binder-aware search-JSON tree is stored on
 * axiom.lemma.meta -> `fingerprint` (a JSON object: the binder-aware toJSON
 * tree, not the fingerprintFormat string).
 *
 * By default `Lemma/Random`, `Lemma/Complex`, `Lemma/Vector`, and
 * `Lemma/Tensor` are indexed:
 *
 *   node mjs/leanInvertedIndex.mjs
 *   node mjs/leanInvertedIndex.mjs --section Tensor
 *   node mjs/leanInvertedIndex.mjs --store-fingerprint
 *   node mjs/leanInvertedIndex.mjs --query 'a ^ 2 + b ^ 2'
 *   node mjs/leanInvertedIndex.mjs --search 'a² + b²' --limit 100
 *
 * Each document is one `lemma main` conclusion. Binders are De Bruijn `?n`;
 * free names are `$n`. A query is shortlisted to rows whose `count` is at
 * least the query's repetition for every operator head and every
 * `parent>child` head edge (CSS-selector style), then exact-matched.
 */
import fs from "fs";
import os from "os";
import path from "path";
import { spawn } from "child_process";
import { fileURLToPath } from "url";
import { compile } from "../js/parser/lean.js";
import { conclusionSearchJson } from "./lemmaPath.mjs";
import { getMysqlPool } from "./lean/fetchLemmaMysql.mjs";
import { REPO_ROOT, leanPathToModule } from "./lean/modulePath.mjs";
import { matchesSubtree } from "./leanSubtreeMatch.mjs";
import { binderQueryVariants, powerQueryVariants } from "./lean/queryExpansion.mjs";

const LEMMA_ROOT = path.join(REPO_ROOT, "Lemma");
export const INDEXED_SECTIONS = ["Random", "Complex", "Vector", "Tensor"];
const INSERT_CHUNK = 500;
const ID_CHUNK = 500;

export function fingerprintFormat(json) {
  if (json == null || json === "") return "";
  if (typeof json === "string") return json;
  if (Array.isArray(json)) return json.map(fingerprintFormat).join("");
  const head = Object.keys(json)[0];
  const children = json[head];
  if (!Array.isArray(children)) return head;
  return head + children.map((c) => {
    const s = fingerprintFormat(c);
    return s === "" ? "" : `(${s})`;
  }).join("");
}

/** Count each operator head in a search-JSON tree. Leaves (`$1`, `?0`, `2`) are ignored. */
export function countHeads(json, counts = new Map()) {
  if (json == null || typeof json !== "object") return counts;
  if (Array.isArray(json)) {
    for (const item of json) countHeads(item, counts);
    return counts;
  }
  for (const [head, args] of Object.entries(json)) {
    counts.set(head, (counts.get(head) ?? 0) + 1);
    countHeads(args, counts);
  }
  return counts;
}

/**
 * Count each `parent>child` head pair in a search-JSON tree. Only object
 * children (heads) are paired: leaves (`$1`, `?0`, `2`) carry no edge, so a
 * query hole never demands an edge the documents cannot have.
 */
export function countEdges(json, edges = new Map()) {
  if (json == null || typeof json !== "object") return edges;
  if (Array.isArray(json)) {
    for (const item of json) countEdges(item, edges);
    return edges;
  }
  for (const [head, args] of Object.entries(json)) {
    for (const child of Array.isArray(args) ? args : [args]) {
      if (child == null || typeof child !== "object" || Array.isArray(child)) continue;
      for (const childHead of Object.keys(child)) {
        const name = `${head}>${childHead}`;
        edges.set(name, (edges.get(name) ?? 0) + 1);
      }
    }
    countEdges(args, edges);
  }
  return edges;
}

export function headsOfQuery(expr) {
  const source = `private lemma main : ${expr} := by\n  sorry\n`;
  const ast = compile(source);
  const lemma = (ast?.args || []).find((a) => {
    const name = a?.constructor?.name;
    return name === "Lean_lemma" || name === "Lean_theorem";
  });
  const assign = (lemma?.args || []).find((a) => a?.constructor?.name === "LeanAssign");
  const colon = (assign?.args || []).find((a) => a?.constructor?.name === "LeanColon");
  let node = colon?.rhs ?? colon?.args?.[colon.args.length - 1];
  while (node && (node.constructor?.name === "LeanStatements" || node.constructor?.name === "LeanArgsNewLineSeparated")) {
    const args = (node.args || []).filter((a) => a?.constructor?.name !== "LeanLineComment");
    node = args[args.length - 1] ?? null;
  }
  while (node?.constructor?.name === "LeanParenthesis") node = node.arg ?? node.args?.[0];
  if (!node?.toJSON) throw new Error("Could not parse the query conclusion");
  return queryFromJson(node.toJSON({ leaves: new Map(), binders: [] }));
}

/** Wrap a search-JSON tree as a query (heads + `parent>child` edges + fingerprint). */
export function queryFromJson(json) {
  return {
    json,
    fingerprint: fingerprintFormat(json),
    counts: countHeads(json),
    edges: countEdges(json),
  };
}

/**
 * Entries for similarity matching: the original query plus every expanded query,
 * deduplicated by fingerprint. Exact search never uses this list.
 * @param {string} expr
 */
export function expandedQueries(expr) {
  const out = [];
  const seen = new Set();
  const add = (query) => {
    if (!query || seen.has(query.fingerprint)) return;
    seen.add(query.fingerprint);
    out.push(query);
  };
  const base = headsOfQuery(expr);
  add(base);
  for (const source of binderQueryVariants(expr)) {
    const query = source === expr ? base : headsOfQuery(source);
    add(query);
    for (const json of powerQueryVariants(query.json)) add(queryFromJson(json));
  }
  return out;
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

function sectionRoot(section) {
  if (!section) return LEMMA_ROOT;
  return path.join(LEMMA_ROOT, section);
}

/**
 * Index one list of files (no MySQL ids yet). The parent looks up lemma.id
 * and uploads postings plus the search-JSON tree.
 */
export function collectConclusions({ files, filter = null } = {}) {
  const entries = [];
  let skipped = 0;
  for (const abs of files) {
    const rel = path.relative(REPO_ROOT, abs).split(path.sep).join("/");
    if (filter && !rel.includes(filter)) continue;
    let json;
    try {
      json = conclusionSearchJson(abs);
    } catch {
      skipped++;
      continue;
    }
    const counts = countHeads(json);
    if (counts.size === 0) {
      skipped++;
      continue;
    }
    const heads = {};
    for (const [head, n] of counts) heads[head] = n;
    const edges = {};
    for (const [edge, n] of countEdges(json)) edges[edge] = n;
    entries.push({
      module: leanPathToModule(rel),
      path: rel,
      json,
      heads,
      edges,
    });
  }
  return { skipped, entries };
}

function requirePool() {
  const pool = getMysqlPool();
  if (!pool) {
    throw new Error("MySQL is not configured; set MYSQL_HOST and MYSQL_PWD (database axiom)");
  }
  return pool;
}

async function mapModulesToIds(pool, modules) {
  const idOf = new Map();
  for (let i = 0; i < modules.length; i += ID_CHUNK) {
    const chunk = modules.slice(i, i + ID_CHUNK);
    const [rows] = await pool.query("SELECT id, module FROM lemma WHERE module IN (?)", [chunk]);
    for (const row of rows) idOf.set(row.module, row.id);
  }
  return idOf;
}

export function parseFingerprint(value) {
  if (value == null || value === "") return null;
  if (typeof value === "string") {
    try {
      return JSON.parse(value);
    } catch {
      return null;
    }
  }
  if (typeof value === "object") return value;
  return null;
}

/** Write each document's fingerprint tree onto axiom.lemma.meta.fingerprint. */
export async function uploadFingerprints(pool, entries) {
  const idOf = await mapModulesToIds(pool, entries.map((e) => e.module));
  let uploaded = 0;
  let missing = 0;
  const conn = await pool.getConnection();
  try {
    await conn.beginTransaction();
    for (const entry of entries) {
      const id = idOf.get(entry.module);
      if (id == null || entry.json == null) {
        if (id == null) missing++;
        continue;
      }
      await conn.query(
        "UPDATE lemma SET meta = JSON_SET(COALESCE(meta, JSON_OBJECT()), '$.fingerprint', CAST(? AS JSON)) WHERE id = ?",
        [JSON.stringify(entry.json), id],
      );
      uploaded++;
    }
    await conn.commit();
  } catch (err) {
    await conn.rollback();
    throw err;
  } finally {
    conn.release();
  }
  return { uploaded, missing };
}

/** True when `module` belongs to an inverted-index section (Random, Complex, Vector, or Tensor). */
export function isIndexedSection(module) {
  const head = String(module ?? "").split(".")[0];
  return INDEXED_SECTIONS.includes(head);
}

function invertedRowsFor(id, heads, edges = new Map()) {
  const rows = [];
  for (const map of [heads, edges]) {
    const entries = map instanceof Map ? map.entries() : Object.entries(map ?? {});
    for (const [name, count] of entries) {
      if (name == null || name === "") continue;
      rows.push([name, id, count]);
    }
  }
  return rows;
}

/**
 * Replace inverted postings for one lemma.id.
 * An empty head list deletes any previous postings and inserts nothing.
 */
export async function replaceInvertedPostings(pool, id, heads, edges = new Map()) {
  await pool.query("DELETE FROM inverted WHERE id = ?", [id]);
  const rows = invertedRowsFor(id, heads, edges);
  if (rows.length === 0) return { postings: 0 };
  await pool.query("INSERT INTO inverted (name, id, count) VALUES ?", [rows]);
  return { postings: rows.length };
}

/**
 * After a lemma upsert: drop this id's postings, then write new ones only
 * when the module is in Random, Complex, Vector, or Tensor and a fingerprint tree is present.
 */
export async function refreshInvertedForLemma(pool, { id, module, json }) {
  const indexed = isIndexedSection(module) && json != null;
  const heads = indexed ? countHeads(json) : new Map();
  const edges = indexed ? countEdges(json) : new Map();
  return replaceInvertedPostings(pool, id, heads, edges);
}

function positiveIds(ids) {
  return [...new Set((ids ?? []).map((id) => Number(id)).filter((id) => Number.isInteger(id) && id > 0))];
}

/** Drop inverted postings for the given lemma.id values. */
export async function deleteInvertedForIds(pool, ids) {
  const list = positiveIds(ids);
  if (!list.length) return { ids: [] };
  await pool.query(`DELETE FROM inverted WHERE id IN (${list.join(",")})`);
  return { ids: list };
}

/**
 * Delete lemma rows and their inverted postings.
 * Pass `modules` for exact module names, or `prefix` for a package (`module` and `module.%`).
 */
export async function deleteLemmaRowsAndInverted(pool, { modules, prefix } = {}) {
  let rows = [];
  if (prefix != null && prefix !== "") {
    const [found] = await pool.query(
      "SELECT id, module FROM lemma WHERE module = ? OR module LIKE ?",
      [prefix, `${prefix}.%`],
    );
    rows = found;
  } else {
    const list = [...new Set((modules ?? []).map((m) => String(m ?? "").trim()).filter(Boolean))];
    if (!list.length) return { deleted: 0, ids: [], modules: [] };
    const [found] = await pool.query(
      `SELECT id, module FROM lemma WHERE module IN (${list.map(() => "?").join(",")})`,
      list,
    );
    rows = found;
  }
  const ids = rows.map((row) => row.id);
  await deleteInvertedForIds(pool, ids);
  if (ids.length) {
    await pool.query(`DELETE FROM lemma WHERE id IN (${ids.join(",")})`);
  }
  return { deleted: ids.length, ids, modules: rows.map((row) => row.module) };
}

/**
 * After a rename that keeps lemma.id: rebuild inverted postings for the new module
 * (no-op rewrite when the section is still indexed; drop postings when it is not).
 */
export async function refreshInvertedForModule(pool, module) {
  const [rows] = await pool.query(
    "SELECT id, module, JSON_EXTRACT(meta, '$.fingerprint') AS fingerprint FROM lemma WHERE module = ?",
    [module],
  );
  if (!rows.length) return { updated: 0 };
  const row = rows[0];
  const result = await refreshInvertedForLemma(pool, {
    id: row.id,
    module: row.module,
    json: parseFingerprint(row.fingerprint),
  });
  return { updated: 1, id: row.id, postings: result.postings };
}

/** Replace postings in `inverted` for the given documents. `id` is `lemma.id`. */
export async function uploadInverted(pool, entries) {
  const idOf = await mapModulesToIds(pool, entries.map((e) => e.module));
  const withId = [];
  let missing = 0;
  for (const entry of entries) {
    const id = idOf.get(entry.module);
    if (id == null) {
      missing++;
      continue;
    }
    withId.push({ ...entry, id });
  }
  const ids = [...new Set(withId.map((e) => e.id))];
  const rows = [];
  for (const entry of withId) {
    rows.push(...invertedRowsFor(entry.id, entry.heads, entry.edges));
  }
  const conn = await pool.getConnection();
  try {
    await conn.beginTransaction();
    for (let i = 0; i < ids.length; i += ID_CHUNK) {
      await conn.query("DELETE FROM inverted WHERE id IN (?)", [ids.slice(i, i + ID_CHUNK)]);
    }
    for (let i = 0; i < rows.length; i += INSERT_CHUNK) {
      await conn.query("INSERT INTO inverted (name, id, count) VALUES ?", [rows.slice(i, i + INSERT_CHUNK)]);
    }
    await conn.commit();
  } catch (err) {
    await conn.rollback();
    throw err;
  } finally {
    conn.release();
  }
  return { uploaded: withId.length, missing, postings: rows.length };
}

/**
 * Documents that contain every query head and every `parent>child` head edge
 * at least as often as the query. Both are necessary conditions for a subtree
 * match, so the result is a superset of the exact hits.
 * @returns {Promise<number[]>}
 */
export async function filterInverted(pool, queryCounts, queryEdges = new Map()) {
  let candidates = null;
  for (const [head, need] of [...queryCounts, ...queryEdges]) {
    const [rows] = await pool.query(
      "SELECT id FROM inverted WHERE name = ? AND count >= ?",
      [head, need],
    );
    const hit = rows.map((row) => row.id);
    candidates = candidates == null ? new Set(hit) : new Set(hit.filter((id) => candidates.has(id)));
    if (candidates.size === 0) return [];
  }
  return [...(candidates ?? [])].sort((a, b) => a - b);
}

async function loadFingerprintsByIds(pool, ids) {
  const docs = [];
  for (let i = 0; i < ids.length; i += ID_CHUNK) {
    const chunk = ids.slice(i, i + ID_CHUNK);
    const [rows] = await pool.query(
      "SELECT id, module, JSON_EXTRACT(meta, '$.fingerprint') AS fingerprint FROM lemma WHERE id IN (?)",
      [chunk],
    );
    docs.push(...rows);
  }
  return docs;
}

/** Shortlist + exact subtree match for one already-parsed query. */
async function searchParsedQuery(query, { limit = 100, db }) {
  const ids = await filterInverted(db, query.counts, query.edges);
  if (ids.length === 0) return { shortlist: 0, hits: [] };
  const docs = await loadFingerprintsByIds(db, ids);
  const hits = [];
  for (const row of docs) {
    const json = parseFingerprint(row.fingerprint);
    if (json == null) continue;
    if (matchesSubtree(query.json, json)) {
      hits.push({ id: row.id, module: row.module });
    }
  }
  hits.sort((a, b) => String(a.module).localeCompare(String(b.module)));
  const cap = Math.max(0, Number(limit) || 0);
  return { shortlist: ids.length, hits: hits.slice(0, cap) };
}

/**
 * Shortlist via axiom.inverted, then exact subtree-match on lemma.meta.fingerprint.
 * Does not close a shared MySQL pool.
 *
 * @param {string} expr
 * @param {{ limit?: number, pool?: import('mysql2/promise').Pool }} [options]
 * @returns {Promise<{ query: { json: object, fingerprint: string, counts: Map<string, number> }, shortlist: number, hits: { id: number, module: string }[] }>}
 */
export async function searchLeanExact(expr, { limit = 100, pool = null } = {}) {
  const db = pool ?? requirePool();
  const query = headsOfQuery(expr);
  return { query, ...(await searchParsedQuery(query, { limit, db })) };
}

/**
 * Exact search on the original query; only when that finds nothing, run the
 * expanded queries from `expandedQueries` and label those results as similar.
 * Similar hits are deduplicated across expansions and against the exact hits.
 *
 * @param {string} expr
 * @param {{ limit?: number, pool?: import('mysql2/promise').Pool }} [options]
 * @returns {Promise<{
 *   query: { json: object, fingerprint: string, counts: Map<string, number>, edges: Map<string, number> },
 *   exact: { id: number, module: string }[],
 *   similar: { id: number, module: string, match: 'similar' }[],
 *   shortlist: number,
 * }>}
 */
export async function searchLeanSimilar(expr, { limit = 100, pool = null } = {}) {
  const db = pool ?? requirePool();
  const exact = await searchLeanExact(expr, { limit, pool: db });
  const similar = [];
  if (exact.hits.length > 0) return { query: exact.query, exact: exact.hits, similar, shortlist: exact.shortlist };

  const seen = new Set(exact.hits.map((hit) => hit.id));
  let shortlist = exact.shortlist;
  for (const query of expandedQueries(expr)) {
    if (query.fingerprint === exact.query.fingerprint) continue;
    const found = await searchParsedQuery(query, { limit, db });
    shortlist += found.shortlist;
    for (const hit of found.hits) {
      if (seen.has(hit.id)) continue;
      seen.add(hit.id);
      similar.push({ ...hit, match: "similar" });
    }
  }
  similar.sort((a, b) => String(a.module).localeCompare(String(b.module)));
  const cap = Math.max(0, Number(limit) || 0);
  return { query: exact.query, exact: exact.hits, similar: similar.slice(0, cap), shortlist };
}

function usage() {
  console.error(`usage: node mjs/leanInvertedIndex.mjs [options]

  --section <name>     index only this lemma section (default: Random, Complex, Vector, Tensor)
  --chunk-size <n>     files per child process (default: 250, 0 = one process)
  --store-fingerprint  write lemma.meta.fingerprint only (do not rebuild inverted)
  --delete-module <m>  delete axiom.lemma row <m> and its inverted postings
  --delete-prefix <m>  delete rows with module = <m> or module like <m>.%
  --refresh-module <m> rebuild inverted postings for one module (same id)
  --query <lean>       shortlist documents in axiom.inverted (heads + parent>child edges)
  --search <lean>      exact subtree-match, then expanded queries as similarity when exact has no hits
  --limit <n>          max hits for --search (default: 100)
  -h, --help           this message`);
}

function parseArgs(argv) {
  const opts = {
    mode: "index",
    section: null,
    chunkSize: 250,
    query: null,
    limit: 100,
    filesFrom: null,
    out: null,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--section") opts.section = argv[++i] || (() => { throw new Error("missing --section name"); })();
    else if (a === "--chunk-size") opts.chunkSize = Number(argv[++i]) || 0;
    else if (a === "--files-from") opts.filesFrom = argv[++i] ?? null;
    else if (a === "--out") opts.out = argv[++i] ?? null;
    else if (a === "--limit") opts.limit = Math.max(0, Number(argv[++i]) || 0);
    else if (a === "--store-fingerprint") opts.mode = "store-fingerprint";
    else if (a === "--delete-module") {
      opts.mode = "delete-module";
      opts.module = argv[++i] ?? "";
    } else if (a === "--delete-prefix") {
      opts.mode = "delete-prefix";
      opts.module = argv[++i] ?? "";
    } else if (a === "--refresh-module") {
      opts.mode = "refresh-module";
      opts.module = argv[++i] ?? "";
    } else if (a === "--query") {
      opts.mode = "query";
      opts.query = argv[++i] ?? "";
    } else if (a === "--search") {
      opts.mode = "search";
      opts.query = argv[++i] ?? "";
    } else if (a === "--index") opts.mode = "index";
    else if (a === "-h" || a === "--help") opts.mode = "help";
    else if (a.startsWith("-")) throw new Error(`unknown option: ${a}`);
    else {
      opts.mode = "query";
      opts.query = a;
    }
  }
  return opts;
}

async function collectSection(opts) {
  const sections = opts.section ? [opts.section] : INDEXED_SECTIONS;
  let files = opts.filesFrom
    ? fs.readFileSync(opts.filesFrom, "utf8").split("\n").filter(Boolean)
    : sections.flatMap((section) => walkLeanFiles(sectionRoot(section))).sort();
  let skipped = 0;
  let entries = [];
  if (!opts.filesFrom && files.length > opts.chunkSize && opts.chunkSize > 0) {
    const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "lean-inv-"));
    const self = fileURLToPath(import.meta.url);
    const chunks = Math.ceil(files.length / opts.chunkSize);
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
  } else {
    const part = collectConclusions({ files });
    entries = part.entries;
    skipped = part.skipped;
    if (opts.filesFrom) {
      if (!opts.out) throw new Error("child index process needs --out");
      fs.writeFileSync(opts.out, JSON.stringify({ skipped, entries }));
      return { entries, skipped, child: true };
    }
  }
  return { entries, skipped, child: false };
}

async function runIndex(opts) {
  const t0 = performance.now();
  const { entries, skipped, child } = await collectSection(opts);
  if (child) return;
  const pool = requirePool();
  const { uploaded, missing, postings } = await uploadInverted(pool, entries);
  const stored = await uploadFingerprints(pool, entries);
  await pool.end();
  console.log(
    `uploaded ${uploaded} documents, ${postings} postings to axiom.inverted ` +
      `and ${stored.uploaded} fingerprint trees ` +
      `(${skipped} parse skipped, ${missing} missing from lemma) in ` +
      `${((performance.now() - t0) / 1000).toFixed(1)}s`,
  );
}

async function runStoreJson(opts) {
  const t0 = performance.now();
  const { entries, skipped, child } = await collectSection(opts);
  if (child) return;
  const pool = requirePool();
  const { uploaded, missing } = await uploadFingerprints(pool, entries);
  await pool.end();
  console.log(
    `stored ${uploaded} fingerprint trees on axiom.lemma.meta ` +
      `(${skipped} parse skipped, ${missing} missing from lemma) in ` +
      `${((performance.now() - t0) / 1000).toFixed(1)}s`,
  );
}

async function runQuery(opts) {
  const pool = requirePool();
  const query = headsOfQuery(opts.query);
  const ids = await filterInverted(pool, query.counts, query.edges);
  const need = [...query.counts].map(([h, n]) => `${h}:${n}`).join(", ");
  const edgeNeed = [...query.edges].map(([e, n]) => `${e}:${n}`).join(", ");
  let docs = [];
  if (ids.length) {
    const [rows] = await pool.query("SELECT id, module FROM lemma WHERE id IN (?)", [ids]);
    const byId = new Map(rows.map((row) => [row.id, row.module]));
    docs = ids.map((id) => ({ id, module: byId.get(id) ?? "?" }));
  }
  await pool.end();
  console.log(`query: ${query.fingerprint}`);
  console.log(`heads: ${need || "(none)"}`);
  console.log(`edges: ${edgeNeed || "(none)"}`);
  console.log(`shortlist: ${docs.length}`);
  for (const doc of docs) console.log(`${doc.id}\t${doc.module}`);
}

async function runSearch(opts) {
  const pool = requirePool();
  try {
    const { query, shortlist, exact, similar } = await searchLeanSimilar(opts.query, { limit: opts.limit, pool });
    const need = [...query.counts].map(([h, n]) => `${h}:${n}`).join(", ");
    const edgeNeed = [...query.edges].map(([e, n]) => `${e}:${n}`).join(", ");
    console.log(`query: ${query.fingerprint}`);
    console.log(`heads: ${need || "(none)"}`);
    console.log(`edges: ${edgeNeed || "(none)"}`);
    console.log(`shortlist: ${shortlist}`);
    console.log(`exact hits: ${exact.length}`);
    for (const hit of exact) console.log(`\t${hit.id}\t${hit.module}`);
    console.log(`similarity hits: ${similar.length}`);
    for (const hit of similar) console.log(`\t[similar]\t${hit.id}\t${hit.module}`);
  } finally {
    await pool.end();
  }
}

async function runDeleteModule(opts) {
  const pool = requirePool();
  try {
    const result = opts.mode === "delete-prefix"
      ? await deleteLemmaRowsAndInverted(pool, { prefix: opts.module })
      : await deleteLemmaRowsAndInverted(pool, { modules: [opts.module] });
    const names = result.modules.join(", ") || "(none)";
    console.log(`deleted ${result.deleted} lemma row(s) and inverted postings: ${names}`);
  } finally {
    await pool.end();
  }
}

async function runRefreshModule(opts) {
  const pool = requirePool();
  try {
    const result = await refreshInvertedForModule(pool, opts.module);
    if (!result.updated) {
      console.log(`no axiom.lemma row for module=${opts.module}`);
      return;
    }
    console.log(`refreshed inverted for id=${result.id} module=${opts.module} postings=${result.postings}`);
  } finally {
    await pool.end();
  }
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
  if (opts.mode === "help") {
    usage();
    return;
  }
  if (opts.mode === "query") {
    if (!opts.query) {
      usage();
      process.exitCode = 2;
      return;
    }
    await runQuery(opts);
    return;
  }
  if (opts.mode === "search") {
    if (!opts.query) {
      usage();
      process.exitCode = 2;
      return;
    }
    await runSearch(opts);
    return;
  }
  if (opts.mode === "store-fingerprint") {
    await runStoreJson(opts);
    return;
  }
  if (opts.mode === "delete-module" || opts.mode === "delete-prefix") {
    if (!opts.module) {
      usage();
      process.exitCode = 2;
      return;
    }
    await runDeleteModule(opts);
    return;
  }
  if (opts.mode === "refresh-module") {
    if (!opts.module) {
      usage();
      process.exitCode = 2;
      return;
    }
    await runRefreshModule(opts);
    return;
  }
  await runIndex(opts);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch((e) => {
    console.error(e.message);
    process.exitCode = 1;
  });
}
