/**
 * Mirrors `request/count` + `request/lines` for the website home labels.
 *
 * - Theorem count: `select count(*) from lemma where json_length(imports) > 0`
 *   rows in `lemma` with imports, not a raw `.lean` file count.
 * - Lines: non-empty lines in all `.lean` under the decl libraries and `Lemma/` except `*.echo.lean`
 *   (`request/lines` + `read_all_lean`).
 */
import fs from 'fs/promises';
import path from 'path';
import { REPO_ROOT } from './modulePath.mjs';
import { getMysqlConfig, getMysqlPool } from './fetchLemmaMysql.mjs';

const LINE_ROOTS = [
  'Lemma',
  'Def', 'Theorem', 'Instance', 'Class', 'Structure', 'Abbrev',
  'Notation', 'Inductive', 'Syntax', 'Macro', 'Initialize',
];
const CACHE_TTL_MS = 5 * 60 * 1000;

/** @type {{ data: { theoremCount: number, lineCount: number }, at: number } | null} */
let cache = null;

async function collectLeanFilesNoEcho(absDir) {
  /** @type {string[]} */
  const out = [];
  let entries;
  try {
    entries = await fs.readdir(absDir, { withFileTypes: true });
  } catch {
    return out;
  }
  for (const ent of entries) {
    const full = path.join(absDir, ent.name);
    if (ent.isDirectory()) {
      out.push(...(await collectLeanFilesNoEcho(full)));
    } else if (
      ent.isFile() &&
      ent.name.endsWith('.lean') &&
      !ent.name.endsWith('.echo.lean')
    ) {
      out.push(full);
    }
  }
  return out;
}

/** Non-empty lines of a file. */
function countNonEmptyLinesBuf(buf) {
  if (buf.length === 0) return 0;
  const s = buf.toString('utf8');
  return s.split(/\r\n|\r|\n/).filter((line) => line.length > 0).length;
}

async function getLeanNonEmptyLinesTotal() {
  let total = 0;
  const batch = 128;
  /** @type {string[]} */
  const files = [];
  for (const rel of LINE_ROOTS) {
    const abs = path.join(REPO_ROOT, rel);
    files.push(...(await collectLeanFilesNoEcho(abs)));
  }
  for (let i = 0; i < files.length; i += batch) {
    const slice = files.slice(i, i + batch);
    const buffers = await Promise.all(slice.map((f) => fs.readFile(f)));
    for (const buf of buffers) {
      total += countNonEmptyLinesBuf(buf);
    }
  }
  return total;
}

/**
 * `select count(*)` over `lemma` rows that have imports, with no type filter.
 */
async function getTheoremCountMysql() {
  if (!getMysqlConfig()) return 0;
  const pool = getMysqlPool();
  if (!pool) return 0;
  try {
    const [rows] = await pool.query(
      'select count(*) as c from lemma where json_length(imports) > 0'
    );
    if (Array.isArray(rows) && rows[0]) {
      return Number(rows[0].c) || 0;
    }
  } catch (e) {
    console.warn('[repo-stats mysql]', e.message);
  }
  return 0;
}

/**
 * @returns {Promise<{ theoremCount: number, lineCount: number }>}
 */
export async function getRepoStats() {
  const [theoremCount, lineCount] = await Promise.all([
    getTheoremCountMysql(),
    getLeanNonEmptyLinesTotal(),
  ]);
  return { theoremCount, lineCount };
}

export async function getRepoStatsCached() {
  const now = Date.now();
  if (cache && now - cache.at < CACHE_TTL_MS) {
    return cache.data;
  }
  const data = await getRepoStats();
  cache = { data, at: now };
  return data;
}
