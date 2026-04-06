/**
 * Mirrors `php/request/count.php` + `php/request/lines.php` for the website home labels.
 *
 * - Theorem count: `select count(*) from lemma where user = ? and json_length(imports) > 0`
 *   (`php/utility.php` `select_count`), not a raw `.lean` file count.
 * - Lines: non-empty lines in all `.lean` under `Lemma/`, `sympy/`, `stdlib/` except `*.echo.lean`
 *   (`php/request/lines.php` + `read_all_lean`).
 */
import fs from 'fs/promises';
import path from 'path';
import { REPO_ROOT } from './modulePath.mjs';
import { getMysqlConfig, getMysqlPool } from './fetchLemmaMysql.mjs';

const LINE_ROOTS = ['Lemma', 'sympy', 'stdlib'];
const CACHE_TTL_MS = 5 * 60 * 1000;

/** @type {Map<string, { data: { theoremCount: number, lineCount: number }, at: number }>} */
const cacheByUser = new Map();

function dbUser(projectUser) {
  const s = String(projectUser || 'lean');
  return /^[a-zA-Z0-9_]+$/.test(s) ? s : 'lean';
}

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

/** PHP `file(..., FILE_IGNORE_NEW_LINES | FILE_SKIP_EMPTY_LINES)` → non-empty line segments. */
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
 * Same as `php/utility.php` `select_count($user)` without type filter.
 * @param {string} projectUser
 */
async function getTheoremCountMysql(projectUser) {
  if (!getMysqlConfig()) return 0;
  const pool = getMysqlPool();
  if (!pool) return 0;
  const u = dbUser(projectUser);
  try {
    const [rows] = await pool.query(
      'select count(*) as c from lemma where user = ? and json_length(imports) > 0',
      [u]
    );
    if (Array.isArray(rows) && rows[0]) {
      return Number(rows[0].c) || 0;
    }
  } catch (e) {
    console.warn('[repo-stats mysql]', /** @type {Error} */ (e).message);
  }
  return 0;
}

/**
 * @param {string} projectUser
 * @returns {Promise<{ theoremCount: number, lineCount: number }>}
 */
export async function getRepoStats(projectUser) {
  const [theoremCount, lineCount] = await Promise.all([
    getTheoremCountMysql(projectUser),
    getLeanNonEmptyLinesTotal(),
  ]);
  return { theoremCount, lineCount };
}

export async function getRepoStatsCached(projectUser) {
  const key = dbUser(projectUser);
  const now = Date.now();
  const hit = cacheByUser.get(key);
  if (hit && now - hit.at < CACHE_TTL_MS) {
    return hit.data;
  }
  const data = await getRepoStats(projectUser);
  cacheByUser.set(key, { data, at: now });
  return data;
}
