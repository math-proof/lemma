#!/usr/bin/env node
/**
 * leanInvertedIndex.mjs
 * =====================
 * Build the inverted index of lemma-conclusion operator heads and upload it
 * to axiom.inverted (`name`, `id`, `lemma_id`, `section`, `latex_id`, `count`),
 * whose `id` is axiom.lemma.id. `lemma_id` is the zero-based declaration index
 * in the Lean file, `section` is `given` / `imply` / `proof`, and `latex_id`
 * is the zero-based latex formula index within that section. The selected
 * declaration contributes every given, every flattened top-level imply
 * conjunct, and every source-level proof step. `lemma_id` is its declaration
 * position (`main` is not necessarily declaration 0).
 * Each selected declaration's binder-aware search-JSON trees are stored in
 * axiom.fingerprint, one row per `(lemma_id, section, latex_id)`: the whole
 * imply conjunction at `latex_id` 0 (preserving exact conclusion search) plus
 * every given/proof formula. `axiom.lemma.meta` no longer holds a fingerprint.
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
 * Each document is one formula from the selected declaration. Binders are De
 * Bruijn `?n`; free names are `$n`. A query is shortlisted to rows whose `count` is at
 * least the query's repetition for every operator head and every
 * `parent>child` head edge (CSS-selector style), then exact-matched.
 */
import fs from "fs";
import os from "os";
import path from "path";
import { spawn } from "child_process";
import { fileURLToPath } from "url";
import { compile } from "../js/parser/lean.js";
import { lemmaSearchDocuments } from "./lemmaPath.mjs";
import { getMysqlPool } from "./lean/fetchLemmaMysql.mjs";
import { REPO_ROOT, leanFilePathToModule, moduleToRepoLeanPath } from "./lean/modulePath.mjs";
import { assembleLeanSourceFromPostBody } from "./lean/assembleLemmaPost.mjs";
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

/**
 * Canonical string form for comparing fingerprint trees across the MySQL round
 * trip: key order is irrelevant, and `undefined` properties (which JSON storage
 * drops) are ignored, so a stored tree compares equal to the tree it was made from.
 */
export function fingerprintSignature(json) {
  if (json == null) return "null";
  if (Array.isArray(json)) {
    return "[" + json.map(item => item === undefined ? "null" : fingerprintSignature(item)).join(",") + "]";
  }
  if (typeof json === "object") {
    return "{" + Object.keys(json)
      .filter(key => json[key] !== undefined)
      .sort()
      .map(key => JSON.stringify(key) + ":" + fingerprintSignature(json[key]))
      .join(",") + "}";
  }
  return JSON.stringify(json);
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

/** Convert extracted section documents into uploadable posting entries. */
function searchEntries(module, extracted, rel = null) {
  const entries = [];
  for (const document of extracted.documents) {
    const heads = {};
    for (const [head, n] of countHeads(document.json)) heads[head] = n;
    const edges = {};
    for (const [edge, n] of countEdges(document.json)) edges[edge] = n;
    if (Object.keys(heads).length === 0 && Object.keys(edges).length === 0) continue;
    entries.push({
      module,
      path: rel,
      json: document.json,
      fingerprint: extracted.fingerprint,
      heads,
      edges,
      lemmaId: document.lemmaId,
      section: document.section,
      latexId: document.latexId,
    });
  }
  return entries;
}

/**
 * Index one list of files (no MySQL ids yet). The parent looks up lemma.id
 * and uploads postings plus the search-JSON tree.
 */
export function collectConclusions({ files, filter = null } = {}) {
  const entries = [];
  const failures = [];
  let skipped = 0;
  for (const abs of files) {
    const rel = path.relative(REPO_ROOT, abs).split(path.sep).join("/");
    if (filter && !rel.includes(filter)) continue;
    let extracted;
    try {
      extracted = lemmaSearchDocuments(abs);
    } catch (error) {
      skipped++;
      failures.push({ path: rel, message: String(error?.message ?? error).split("\n")[0] });
      continue;
    }
    const added = searchEntries(leanFilePathToModule(abs), extracted, rel);
    entries.push(...added);
    if (added.length === 0) skipped++;
  }
  return { skipped, entries, failures };
}

async function collectStoredConclusions(pool, { id, module }) {
  const [rows] = await pool.query("SELECT * FROM lemma WHERE id = ?", [id]);
  if (!rows.length) throw new Error("Lemma row not found");
  const row = rows[0];
  const lemmas = typeof row.lemma === "string" ? JSON.parse(row.lemma) : row.lemma;
  if (!Array.isArray(lemmas) || lemmas.length === 0) throw new Error("Stored lemma is empty");
  const source = await assembleLeanSourceFromPostBody({
    ...row,
    lemma: lemmas.map((lemma) => ({
      ...lemma,
      given: Array.isArray(lemma.given) ? lemma.given.map((given) => given?.lean ?? given) : lemma.given,
    })),
  });
  const extracted = lemmaSearchDocuments(`${module}.lean`, undefined, { source });
  return searchEntries(module, extracted);
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

/**
 * Rows for `axiom.fingerprint`: the whole imply tree at `latex_id` 0 plus one
 * tree per given/proof formula. Imply conjuncts are skipped because their
 * aggregate conclusion is the whole tree; `inverted` still keeps every
 * conjunct's postings.
 */
function fingerprintRowsFor(id, json, documents = null, lemmaId = null) {
  if (json == null) return [];
  const declarationId = lemmaId ?? documents?.[0]?.lemmaId ?? 0;
  const rows = new Map();
  rows.set(`${declarationId}|imply|0`, [id, declarationId, "imply", 0, JSON.stringify(json)]);
  for (const document of documents ?? []) {
    if (document.section === "imply" || document.json == null) continue;
    const rowLemmaId = document.lemmaId ?? declarationId;
    const section = document.section;
    const latexId = document.latexId ?? 0;
    rows.set(
      `${rowLemmaId}|${section}|${latexId}`,
      [id, rowLemmaId, section, latexId, JSON.stringify(document.json)],
    );
  }
  return [...rows.values()];
}

/** Replace one lemma's fingerprint trees; the caller owns the transaction. */
async function replaceFingerprints(conn, id, json, documents = null, lemmaId = null) {
  await conn.query("DELETE FROM fingerprint WHERE id = ?", [id]);
  const rows = fingerprintRowsFor(id, json, documents, lemmaId);
  for (let i = 0; i < rows.length; i += INSERT_CHUNK) {
    await conn.query(
      "INSERT INTO fingerprint (id, lemma_id, section, latex_id, fingerprint) VALUES ?",
      [rows.slice(i, i + INSERT_CHUNK)],
    );
  }
  return rows.length;
}

/** Write each lemma's section fingerprints onto axiom.fingerprint. */
export async function uploadFingerprints(pool, entries) {
  const idOf = await mapModulesToIds(pool, entries.map((e) => e.module));
  const byId = new Map();
  let missing = 0;
  for (const entry of entries) {
    const id = idOf.get(entry.module);
    if (id == null) {
      missing++;
      continue;
    }
    const group = byId.get(id) ?? { json: entry.fingerprint ?? entry.json, documents: [] };
    group.documents.push(entry);
    byId.set(id, group);
  }
  const conn = await pool.getConnection();
  try {
    await conn.beginTransaction();
    let stored = 0;
    for (const [id, { json, documents }] of byId) {
      stored += await replaceFingerprints(conn, id, json, documents);
    }
    await conn.commit();
    return { uploaded: byId.size, stored, missing };
  } catch (err) {
    await conn.rollback();
    throw err;
  } finally {
    conn.release();
  }
}

/** True when `module` belongs to an inverted-index section (Random, Complex, Vector, or Tensor). */
export function isIndexedSection(module) {
  const head = String(module ?? "").split(".")[0];
  return INDEXED_SECTIONS.includes(head);
}

/**
 * Posting rows in `inverted` column order: name, id, lemma_id, section,
 * latex_id, count. `location` is the declaration/formula the heads came from;
 * the default is the file's first imply conclusion.
 */
function invertedRowsFor(id, heads, edges = new Map(), location = {}) {
  const { lemmaId = 0, section = "imply", latexId = 0 } = location;
  const rows = [];
  for (const map of [heads, edges]) {
    const entries = map instanceof Map ? map.entries() : Object.entries(map ?? {});
    for (const [name, count] of entries) {
      if (name == null || name === "") continue;
      rows.push([name, id, lemmaId, section, latexId, count]);
    }
  }
  return rows;
}

/**
 * Replace inverted postings for one lemma.id.
 * An empty head list deletes any previous postings and inserts nothing.
 * The caller must hold a transaction and the lemma row lock if readers must
 * never observe the empty intermediate state.
 */
export async function replaceInvertedPostings(pool, id, heads, edges = new Map(), location = {}) {
  await pool.query("DELETE FROM inverted WHERE id = ?", [id]);
  const rows = invertedRowsFor(id, heads, edges, location);
  if (rows.length === 0) return { postings: 0 };
  await pool.query("INSERT INTO inverted (name, id, lemma_id, section, latex_id, count) VALUES ?", [rows]);
  return { postings: rows.length };
}

async function replaceInvertedDocuments(conn, id, documents) {
  await conn.query("DELETE FROM inverted WHERE id = ?", [id]);
  const rows = documents.flatMap((document) => invertedRowsFor(
    id,
    countHeads(document.json),
    countEdges(document.json),
    document,
  ));
  for (let i = 0; i < rows.length; i += INSERT_CHUNK) {
    await conn.query(
      "INSERT INTO inverted (name, id, lemma_id, section, latex_id, count) VALUES ?",
      [rows.slice(i, i + INSERT_CHUNK)],
    );
  }
  return { postings: rows.length, documents: documents.length };
}

/** Run `fn(conn)` inside one transaction; commits on success, rolls back on error. */
async function inTransaction(pool, fn) {
  const conn = typeof pool.getConnection === "function" ? await pool.getConnection() : pool;
  const own = conn !== pool;
  try {
    await conn.beginTransaction();
    const out = await fn(conn);
    await conn.commit();
    return out;
  } catch (err) {
    await conn.rollback();
    throw err;
  } finally {
    if (own) conn.release();
  }
}

/**
 * Write one lemma's fingerprint and postings. The caller must already hold a
 * transaction and the lemma row lock, so both become visible in one commit.
 * `startedAt` (ms, job start) is stored as `meta.revision`: an older job that
 * acquires the lock last must see a higher stored revision and discard itself.
 */
export async function writeLemmaIndex(conn, { id, module, json, documents = null, startedAt = null, location = {} }) {
  if (startedAt != null) {
    await conn.query(
      "UPDATE lemma SET meta = JSON_SET(COALESCE(meta, JSON_OBJECT()), '$.revision', ?) WHERE id = ?",
      [startedAt, id],
    );
  }
  const fingerprints = await replaceFingerprints(conn, id, json, documents, location.lemmaId ?? null);
  const indexed = isIndexedSection(module) && json != null;
  if (documents != null) {
    return { ...(await replaceInvertedDocuments(conn, id, indexed ? documents : [])), fingerprints };
  }
  const heads = indexed ? countHeads(json) : new Map();
  const edges = indexed ? countEdges(json) : new Map();
  return { ...(await replaceInvertedPostings(conn, id, heads, edges, location)), fingerprints };
}

/**
 * Incrementally rebuild one lemma: lock its row, discard the result when a
 * newer build (higher stored revision) already won, then replace fingerprint
 * and postings atomically. Retrying the same accepted revision is idempotent.
 */
export async function refreshInvertedForLemma(pool, { id, module, json, documents = null, startedAt = null, location = {} }) {
  return inTransaction(pool, async (conn) => {
    const [rows] = await conn.query(
      "SELECT JSON_EXTRACT(meta, '$.revision') AS revision FROM lemma WHERE id = ? FOR UPDATE",
      [id],
    );
    if (!rows.length) return { postings: 0, missing: true };
    if (startedAt != null && Number(rows[0].revision ?? 0) > Number(startedAt)) {
      return { postings: 0, stale: true };
    }
    return writeLemmaIndex(conn, { id, module, json, documents, startedAt, location });
  });
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
  return inTransaction(pool, async (conn) => {
    let rows = [];
    if (prefix != null && prefix !== "") {
      const [found] = await conn.query(
        "SELECT id, module FROM lemma WHERE module = ? OR module LIKE ?",
        [prefix, `${prefix}.%`],
      );
      rows = found;
    } else {
      const list = [...new Set((modules ?? []).map((m) => String(m ?? "").trim()).filter(Boolean))];
      if (!list.length) return { deleted: 0, ids: [], modules: [] };
      const [found] = await conn.query(
        `SELECT id, module FROM lemma WHERE module IN (${list.map(() => "?").join(",")})`,
        list,
      );
      rows = found;
    }
    const ids = rows.map((row) => row.id);
    await deleteInvertedForIds(conn, ids);
    if (ids.length) {
      await conn.query(`DELETE FROM fingerprint WHERE id IN (${ids.join(",")})`);
      await conn.query(`DELETE FROM lemma WHERE id IN (${ids.join(",")})`);
    }
    return { deleted: ids.length, ids, modules: rows.map((row) => row.module) };
  });
}

/**
 * After a rename that keeps lemma.id: rebuild inverted postings for the new module
 * (no-op rewrite when the section is still indexed; drop postings when it is not).
 */
export async function refreshInvertedForModule(pool, module) {
  const abs = moduleToRepoLeanPath(module);
  if (!abs) throw new Error(`No Lean source for module=${module}`);
  const { fingerprint, documents } = lemmaSearchDocuments(abs);
  return inTransaction(pool, async (conn) => {
    const [rows] = await conn.query(
      "SELECT id, module FROM lemma WHERE module = ? FOR UPDATE",
      [module],
    );
    if (!rows.length) return { updated: 0 };
    const row = rows[0];
    const result = await writeLemmaIndex(conn, {
      id: row.id,
      module: row.module,
      json: fingerprint,
      documents,
    });
    return { updated: 1, id: row.id, postings: result.postings };
  });
}

/**
 * Replace postings in `inverted` and trees in `fingerprint` for the given
 * documents in ONE transaction, so a live reader never sees new postings with
 * old fingerprints (or the reverse) during a section rebuild. `id` is `lemma.id`.
 */
export async function uploadIndex(pool, entries) {
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
  const rows = withId.flatMap((entry) => invertedRowsFor(entry.id, entry.heads, entry.edges, entry));
  const byId = new Map();
  for (const entry of withId) {
    const group = byId.get(entry.id) ?? { json: entry.fingerprint ?? entry.json, documents: [] };
    group.documents.push(entry);
    byId.set(entry.id, group);
  }
  const conn = await pool.getConnection();
  try {
    await conn.beginTransaction();
    for (const [id, group] of byId) {
      await replaceFingerprints(conn, id, group.json, group.documents);
    }
    for (let i = 0; i < ids.length; i += ID_CHUNK) {
      await conn.query("DELETE FROM inverted WHERE id IN (?)", [ids.slice(i, i + ID_CHUNK)]);
    }
    for (let i = 0; i < rows.length; i += INSERT_CHUNK) {
      await conn.query("INSERT INTO inverted (name, id, lemma_id, section, latex_id, count) VALUES ?", [rows.slice(i, i + INSERT_CHUNK)]);
    }
    await conn.commit();
    return { uploaded: withId.length, missing, postings: rows.length, stored: byId.size };
  } catch (err) {
    await conn.rollback();
    throw err;
  } finally {
    conn.release();
  }
}

/**
 * Documents that contain every query head and every `parent>child` head edge
 * at least as often as the query. Both are necessary conditions for a subtree
 * match, so the result is a superset of the exact hits.
 * @returns {Promise<number[]>}
 */
export async function filterInverted(pool, queryCounts, queryEdges = new Map(), sections = ["imply"]) {
  let candidates = null;
  for (const [head, need] of [...queryCounts, ...queryEdges]) {
    const [rows] = await pool.query(
      "SELECT id FROM inverted WHERE name = ? AND count >= ? AND section IN (?)",
      [head, need, sections],
    );
    const hit = rows.map((row) => row.id);
    candidates = candidates == null ? new Set(hit) : new Set(hit.filter((id) => candidates.has(id)));
    if (candidates.size === 0) return [];
  }
  // Shortlist order doesn't matter: only the final matched hits are sorted
  // (by fingerprint byte length, then module) in searchParsedQuery.
  return [...(candidates ?? [])];
}

async function loadFingerprintsByIds(pool, ids, sections = ["imply"]) {
  const docs = [];
  for (let i = 0; i < ids.length; i += ID_CHUNK) {
    const chunk = ids.slice(i, i + ID_CHUNK);
    // The imply section is stored per flattened conjunct; latex_id 0 holds the
    // whole conjunction, which is the only tree exact search should compare.
    const [rows] = await pool.query(
      "SELECT f.id, l.module, f.fingerprint, f.section, f.lemma_id, f.latex_id " +
        "FROM fingerprint f JOIN lemma l ON l.id = f.id " +
        "WHERE f.id IN (?) AND f.section IN (?) " +
        "AND (f.section <> 'imply' OR f.latex_id = 0)",
      [chunk, sections],
    );
    docs.push(...rows);
  }
  return docs;
}

/**
 * Order final matched hits: smallest conclusion fingerprint first (simplest
 * structure), then module name as a deterministic tie-break so equal-length
 * conclusions never come back in a different order between runs.
 */
function compareHit(a, b) {
  const d = (a.len ?? 0) - (b.len ?? 0);
  if (d !== 0) return d;
  return String(a.module).localeCompare(String(b.module));
}

/** Shortlist + exact subtree match for one already-parsed query. */
async function searchParsedQuery(query, { limit = 100, offset = 0, db, sections = ["imply"] }) {
  // A top-level conjunction is indexed as separate imply formulas, so its root
  // `And` and aggregate head counts are not present at any one latex_id. Exact
  // matching still uses the whole-imply tree stored at imply/latex_id 0.
  const wholeConjunction =
    sections.includes("imply") &&
    query.json &&
    !Array.isArray(query.json) &&
    Object.keys(query.json)[0] === "And";
  let ids;
  if (wholeConjunction) {
    const [rows] = await db.query(
      "SELECT DISTINCT id FROM fingerprint WHERE section = 'imply' AND latex_id = 0",
    );
    ids = rows.map((row) => row.id);
  } else {
    ids = await filterInverted(db, query.counts, query.edges, sections);
  }
  if (ids.length === 0) return { shortlist: 0, hits: [] };
  const docs = await loadFingerprintsByIds(db, ids, sections);
  const hits = [];
  const seen = new Set();
  for (const row of docs) {
    const json = parseFingerprint(row.fingerprint);
    if (json == null) continue;
    if (matchesSubtree(query.json, json) && !seen.has(row.id)) {
      seen.add(row.id);
      hits.push({
        id: row.id,
        module: row.module,
        len: Buffer.byteLength(fingerprintFormat(json)),
        section: row.section,
        lemmaId: row.lemma_id,
        latexId: row.latex_id,
      });
    }
  }
  hits.sort(compareHit);
  const cap = Math.max(0, Number(limit) || 0);
  const start = Math.max(0, Number(offset) || 0);
  return { shortlist: ids.length, total: hits.length, hits: hits.slice(start, start + cap) };
}

/**
 * Run read-only queries against one repeatable-read snapshot, so the shortlist
 * and the fingerprint fetch come from the same committed revision. Callers
 * that already hold a connection (an outer snapshot) are passed through.
 */
async function readSnapshot(db, fn) {
  if (typeof db.getConnection !== "function") return fn(db);
  const conn = await db.getConnection();
  try {
    await conn.query("START TRANSACTION WITH CONSISTENT SNAPSHOT, READ ONLY");
    const out = await fn(conn);
    await conn.commit();
    return out;
  } catch (err) {
    await conn.rollback();
    throw err;
  } finally {
    conn.release();
  }
}

/**
 * Shortlist via axiom.inverted, then exact subtree-match on axiom.fingerprint.
 * Does not close a shared MySQL pool.
 *
 * @param {string} expr
 * @param {{ limit?: number, pool?: import('mysql2/promise').Pool }} [options]
 * @returns {Promise<{ query: { json: object, fingerprint: string, counts: Map<string, number> }, shortlist: number, hits: { id: number, module: string }[] }>}
 */
export async function searchLeanExact(expr, { limit = 100, offset = 0, pool = null, sections = ["imply"] } = {}) {
  const db = pool ?? requirePool();
  const query = headsOfQuery(expr);
  const result = await readSnapshot(db, (conn) => searchParsedQuery(query, { limit, offset, db: conn, sections }));
  return { query, ...result };
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
export async function searchLeanSimilar(expr, { limit = 100, offset = 0, pool = null, sections = ["imply"] } = {}) {
  const db = pool ?? requirePool();
  const start = Math.max(0, Number(offset) || 0);
  const cap = Math.max(0, Number(limit) || 0);
  return readSnapshot(db, async (conn) => {
    const exact = await searchLeanExact(expr, { limit: cap, offset: start, pool: conn, sections });
    const similar = [];
    if ((exact.total ?? exact.hits.length) > 0) {
      return {
        query: exact.query,
        exact: exact.hits,
        similar,
        shortlist: exact.shortlist,
        total: exact.total,
        exactTotal: exact.total,
        more: exact.total > start + exact.hits.length,
      };
    }

    const seen = new Set();
    let shortlist = exact.shortlist;
    // Page 1 keeps the previous per-expansion cap. Later pages read far enough
    // to fill `start + cap` after the expansions are merged.
    const fetchLimit = start + cap;
    let capped = false;
    for (const query of expandedQueries(expr)) {
      if (query.fingerprint === exact.query.fingerprint) continue;
      const found = await searchParsedQuery(query, { limit: fetchLimit, db: conn, sections });
      shortlist += found.shortlist;
      if ((found.total ?? found.hits.length) > fetchLimit) capped = true;
      for (const hit of found.hits) {
        if (seen.has(hit.id)) continue;
        seen.add(hit.id);
        // Keep the expansion that matched: search-result rendering must look for
        // this tree, not the original expression (`a²+b²` is `Square`; the hit
        // stores `Pow` after expansion).
        similar.push({ ...hit, match: "similar", queryJson: query.json });
      }
    }
    similar.sort(compareHit);
    const page = similar.slice(start, start + cap);
    return {
      query: exact.query,
      exact: exact.hits,
      similar: page,
      shortlist,
      total: similar.length,
      exactTotal: 0,
      more: similar.length > start + cap || (capped && page.length === cap),
    };
  });
}

function usage() {
  console.error(`usage: node mjs/leanInvertedIndex.mjs [options]

  --section <name>     index only this lemma section (default: Random, Complex, Vector, Tensor)
  --existing-ids       rebuild every id already present in axiom.inverted
  --chunk-size <n>     files per child process (default: 250, 0 = one process)
  --store-fingerprint  write axiom.fingerprint only (do not rebuild inverted)
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
    existingIds: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--section") opts.section = argv[++i] || (() => { throw new Error("missing --section name"); })();
    else if (a === "--chunk-size") opts.chunkSize = Number(argv[++i]) || 0;
    else if (a === "--files-from") opts.filesFrom = argv[++i] ?? null;
    else if (a === "--out") opts.out = argv[++i] ?? null;
    else if (a === "--limit") opts.limit = Math.max(0, Number(argv[++i]) || 0);
    else if (a === "--existing-ids") opts.existingIds = true;
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
  let files;
  let targetIds = null;
  const failures = [];
  const storedEntries = [];
  if (opts.existingIds && !opts.filesFrom) {
    const pool = opts.db ?? requirePool();
    const [rows] = await pool.query(
      "SELECT DISTINCT l.id, l.module FROM inverted i JOIN lemma l ON l.id = i.id ORDER BY l.id",
    );
    targetIds = rows.length;
    const seen = new Set();
    for (const row of rows) {
      const abs = moduleToRepoLeanPath(row.module);
      if (!abs) {
        try {
          storedEntries.push(...await collectStoredConclusions(pool, row));
        } catch (error) {
          failures.push({
            id: row.id,
            module: row.module,
            message: `Lean source not found; stored lemma fallback failed: ${String(error?.message ?? error).split("\n")[0]}`,
          });
        }
        continue;
      }
      if (!seen.has(abs)) {
        seen.add(abs);
        files ??= [];
        files.push(abs);
      }
    }
    files = (files ?? []).sort();
  } else {
    files = opts.filesFrom
      ? fs.readFileSync(opts.filesFrom, "utf8").split("\n").filter(Boolean)
      : sections.flatMap((section) => walkLeanFiles(sectionRoot(section))).sort();
  }
  let skipped = 0;
  let entries = [...storedEntries];
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
          failures.push(...(part.failures ?? []));
          skipped += part.skipped;
          done++;
          console.error(`  chunk ${done}/${chunks}: ${part.entries.length} documents`);
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
    failures.push(...part.failures);
    if (opts.filesFrom) {
      if (!opts.out) throw new Error("child index process needs --out");
      fs.writeFileSync(opts.out, JSON.stringify({ skipped, entries, failures }));
      return { entries, skipped, failures, child: true };
    }
  }
  return { entries, skipped, failures, targetIds, child: false };
}

async function runIndex(opts) {
  const t0 = performance.now();
  const pool = requirePool();
  try {
    const { entries, skipped, failures, targetIds, child } = await collectSection({ ...opts, db: pool });
    if (child) return;
    const { uploaded, missing, postings, stored } = await uploadIndex(pool, entries);
    console.log(
      `uploaded ${uploaded} documents, ${postings} postings to axiom.inverted ` +
        `and fingerprints for ${stored} lemma(s) on axiom.fingerprint ` +
        `(${targetIds == null ? "" : `${targetIds} existing ids, `}${skipped} parse skipped, ${missing} missing from lemma) in ` +
        `${((performance.now() - t0) / 1000).toFixed(1)}s`,
    );
    if (failures.length) {
      const report = path.join(REPO_ROOT, "tmp", "inverted-reindex-failures.json");
      fs.mkdirSync(path.dirname(report), { recursive: true });
      fs.writeFileSync(report, JSON.stringify({ count: failures.length, failures }, null, 2) + "\n");
      console.error(`${failures.length} source/parse failure(s): ${report}`);
    }
  } finally {
    await pool.end();
  }
}

async function runStoreJson(opts) {
  const t0 = performance.now();
  const pool = requirePool();
  try {
    const { entries, skipped, child } = await collectSection({ ...opts, db: pool });
    if (child) return;
    const { uploaded, stored, missing } = await uploadFingerprints(pool, entries);
    console.log(
      `stored ${stored} fingerprint trees for ${uploaded} lemma(s) on axiom.fingerprint ` +
        `(${skipped} parse skipped, ${missing} missing from lemma) in ` +
        `${((performance.now() - t0) / 1000).toFixed(1)}s`,
    );
  } finally {
    await pool.end();
  }
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
