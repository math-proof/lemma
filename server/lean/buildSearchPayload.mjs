/**
 * Port of `php/search.php` MySQL branches for GET/POST search (type / like / regex).
 * `fullText` (grep) and `latex` similarity are not implemented here yet (empty `data`).
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';

/** @param {unknown} o @param {string} k */
function hasKey(o, k) {
  return o != null && typeof o === 'object' && Object.prototype.hasOwnProperty.call(o, k);
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} user
 * @param {number} limit
 */
async function queryMissing(pool, user, limit) {
  const sql = `
SELECT module
FROM lemma
WHERE user = ? AND json_length(imports) > 0 AND json_length(lemma) = 0
LIMIT ?`;
  const [rows] = await pool.query(sql, [user, limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} user
 * @param {string} type
 * @param {number} limit
 */
async function queryByType(pool, user, type, limit) {
  const sql = `
WITH _t_matrix AS (
  SELECT module, jt.type AS type
  FROM lemma
  CROSS JOIN JSON_TABLE(
    error,
    '$[*]' COLUMNS (type VARCHAR(191) PATH '$.type')
  ) AS jt
  WHERE user = ?
)
SELECT DISTINCT module
FROM _t_matrix
WHERE type = ?
ORDER BY module
LIMIT ?`;
  const [rows] = await pool.query(sql, [user, type, limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} user
 * @param {string} keyword
 * @param {boolean} binary
 * @param {number} limit
 */
async function queryByLike(pool, user, keyword, binary, limit) {
  const esc = String(keyword).replace(/\\/g, '\\\\').replace(/_/g, '\\_').replace(/%/g, '\\%');
  const pattern = `%${esc}%`;
  const sql = binary
    ? 'SELECT module FROM lemma WHERE user = ? AND module LIKE BINARY ? LIMIT ?'
    : 'SELECT module FROM lemma WHERE user = ? AND module LIKE ? LIMIT ?';
  const [rows] = await pool.query(sql, [user, pattern, limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} user
 * @param {string} pattern
 * @param {boolean} binary
 * @param {number} limit
 * @param {boolean} requireImports
 */
async function queryByRegexp(pool, user, pattern, binary, limit, requireImports) {
  let where = binary
    ? 'user = ? AND module REGEXP ? COLLATE utf8mb4_bin'
    : 'user = ? AND module REGEXP ?';
  if (requireImports) where += ' AND json_length(imports) > 0';
  const sql = `SELECT module FROM lemma WHERE ${where} LIMIT ?`;
  const [rows] = await pool.query(sql, [user, pattern, limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {Record<string, unknown>} rawDict
 * @param {string} projectUser
 */
export async function buildSearchPayload(rawDict, projectUser) {
  /** @type {Record<string, unknown>} */
  const dict = { ...rawDict };

  let fullText = false;
  /** @type {string | null} */
  let fullTextPattern = null;
  /** @type {string | null} */
  let latex = null;
  /** @type {string | undefined} */
  let type;

  if (hasKey(dict, 'q')) {
    if (dict.fullText === 'on') {
      fullText = true;
      fullTextPattern = String(dict.q);
    } else if (dict.latex === 'on') {
      latex = String(dict.q);
    }
  } else {
    if (hasKey(dict, 'type')) {
      type = String(dict.type);
      dict.q = null;
    } else if (hasKey(dict, 'latex')) {
      latex = String(dict.latex);
      if (dict.q) {
        latex = String(dict.q);
      } else {
        dict.q = null;
      }
    } else {
      dict.q = '.*';
      dict.regularExpression = true;
    }
  }

  const qForVue =
    dict.q !== undefined && dict.q !== null && String(dict.q) !== '' ? String(dict.q) : null;

  const caseSensitive = hasKey(dict, 'caseSensitive');
  const wholeWord = hasKey(dict, 'wholeWord');
  const regularExpression = hasKey(dict, 'regularExpression');
  const replacement = dict.replacement != null && String(dict.replacement) !== '' ? String(dict.replacement) : null;
  const limit = Math.min(1000, Math.max(1, Number(dict.limit) || 100));

  let regex = qForVue;
  let like = false;
  if (wholeWord && regex != null) {
    regex = `\\b${regex}\\b`;
  } else if (regularExpression && regex != null) {
    regex = regex.replace(/\\/g, '\\\\');
  } else {
    like = true;
  }

  /** @type {{ module: string }[]} */
  let data = [];

  if (fullText && fullTextPattern) {
    data = [];
  } else if (latex) {
    data = [];
  } else {
    const pool = getMysqlPool();
    if (pool) {
      try {
        if (like) {
          if (regex == null || regex === '') {
            if (type === 'missing') {
              data = await queryMissing(pool, projectUser, limit);
            } else if (type != null) {
              data = await queryByType(pool, projectUser, type, limit);
            }
          } else {
            data = await queryByLike(pool, projectUser, regex, caseSensitive, limit);
            if (
              data.length === 0 &&
              !caseSensitive &&
              regex.includes(' ')
            ) {
              const alt = regex.replace(/ /g, '.*');
              data = await queryByRegexp(pool, projectUser, alt, caseSensitive, limit, !!replacement);
            }
          }
        } else if (regex != null) {
          data = await queryByRegexp(pool, projectUser, regex, caseSensitive, limit, !!replacement);
        }
      } catch (e) {
        console.warn('[search]', /** @type {Error} */ (e).message);
        data = [];
      }
    }
  }

  return {
    data,
    user: projectUser,
    q: qForVue,
    regularExpression,
    wholeWord,
    caseSensitive,
    fullText: !!fullText,
    latex,
    replacement,
    limit,
  };
}

/**
 * True when `php/index.php` would load `php/search.php` instead of summary/lemma.
 * @param {Record<string, unknown>} q
 * @param {string} [moduleRaw]
 */
export function leanGetWantsSearch(q, moduleRaw) {
  if (moduleRaw != null && String(moduleRaw).trim() !== '') return false;
  if (q.type != null && String(q.type).trim() !== '') return true;
  if (q.q != null && String(q.q).trim() !== '') return true;
  if (q.latex != null && String(q.latex).trim() !== '') return true;
  if (q.fullText === 'on' && q.q != null && String(q.q).trim() !== '') return true;
  return false;
}
