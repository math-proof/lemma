/**
 * Port of php/search.php: MySQL (type / like / regex) + filesystem full-text under Lemma/.
 * `?lean=<expression>` (or the search box's Lean checkbox) is an exact
 * subtree-match over lemma conclusions: shortlist via axiom.inverted, then
 * match stored axiom.lemma.meta.fingerprint trees (mjs/leanInvertedIndex.mjs).
 * When the exact query has no hit, expanded queries (`∑`/`∏` binder forms,
 * `x²` <-> `x ^ 2`, …) are tried and returned separately as `similar`.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';
import { searchLemmaFullText } from './lemmaFullTextSearch.mjs';
import { moduleToLeanPath, fileExists } from './modulePath.mjs';

/** `lean` values that mean "the checkbox is on"; the expression is in `q`. */
const LEAN_OPTION_FLAGS = new Set(['on', 'true', '1', '']);

/** True when `Lemma/…/Module.lean` exists for a dotted module name. */
function moduleFileExists(module) {
  const abs = moduleToLeanPath(module);
  return abs != null && fileExists(abs);
}

/** @param {unknown} o @param {string} k */
function hasKey(o, k) {
  return o != null && typeof o === 'object' && Object.prototype.hasOwnProperty.call(o, k);
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {number} limit
 */
async function queryMissing(pool, limit) {
  const sql = `
SELECT module
FROM lemma
WHERE json_length(imports) > 0 AND json_length(lemma) = 0
LIMIT ?`;
  const [rows] = await pool.query(sql, [limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} type
 * @param {number} limit
 */
async function queryByType(pool, type, limit) {
  const sql = `
WITH _t_matrix AS (
  SELECT module, jt.type AS type
  FROM lemma
  CROSS JOIN JSON_TABLE(
    JSON_EXTRACT(meta, '$.error'),
    '$[*]' COLUMNS (type VARCHAR(191) PATH '$.type')
  ) AS jt
)
SELECT DISTINCT module
FROM _t_matrix
WHERE type = ?
ORDER BY module
LIMIT ?`;
  const [rows] = await pool.query(sql, [type, limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} keyword
 * @param {boolean} binary
 * @param {number} limit
 */
async function queryByLike(pool, keyword, binary, limit) {
  const esc = String(keyword).replace(/\\/g, '\\\\').replace(/_/g, '\\_').replace(/%/g, '\\%');
  const pattern = `%${esc}%`;
  const sql = binary
    ? 'SELECT module FROM lemma WHERE module LIKE BINARY ? LIMIT ?'
    : 'SELECT module FROM lemma WHERE module LIKE ? LIMIT ?';
  const [rows] = await pool.query(sql, [pattern, limit]);
  return Array.isArray(rows) ? /** @type {{ module: string }[]} */ (rows) : [];
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} pattern
 * @param {boolean} binary
 * @param {number} limit
 * @param {boolean} requireImports
 */
async function queryByRegexp(pool, pattern, binary, limit, requireImports) {
  let where = binary
    ? 'module REGEXP ? COLLATE utf8mb4_bin'
    : 'module REGEXP ?';
  if (requireImports) where += ' AND json_length(imports) > 0';
  const sql = `SELECT module FROM lemma WHERE ${where} LIMIT ?`;
  const [rows] = await pool.query(sql, [pattern, limit]);
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
  let lean = null;
  /** @type {string | undefined} */
  let type;

  // `?lean=<expression>` (URL) or `?q=<expression>&lean=on` (search-box checkbox):
  // exact subtree-match over lemma conclusions, see mjs/leanInvertedIndex.mjs.
  const leanFlag = hasKey(dict, 'lean') ? String(dict.lean ?? '').trim() : null;
  if (leanFlag !== null) {
    const expression = LEAN_OPTION_FLAGS.has(leanFlag) ? String(dict.q ?? '').trim() : leanFlag;
    if (expression) {
      lean = expression;
      dict.q = expression;
    }
  }

  if (hasKey(dict, 'q')) {
    if (dict.fullText === 'on') {
      fullText = true;
      fullTextPattern = String(dict.q);
    }
  } else {
    if (hasKey(dict, 'type')) {
      type = String(dict.type);
      dict.q = null;
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
    // regex = regex.replace(/\\/g, '\\\\');
  } else {
    like = true;
  }

  /** @type {{ module: string }[]} */
  let data = [];
  /** @type {{ module: string, id?: number, match?: string }[]} */
  let exact = [];
  /** @type {{ module: string, id?: number, match?: string }[]} */
  let similar = [];

  if (lean) {
    try {
      const { searchLeanSimilar } = await import('../leanInvertedIndex.mjs');
      const pool = getMysqlPool();
      const result = await searchLeanSimilar(lean, { limit, pool });
      exact = result.exact.map((hit) => ({ ...hit, match: 'exact' }));
      similar = result.similar;
      data = exact.length > 0 ? exact : similar;
    } catch (e) {
      console.warn('[lean-search]', e.message);
      data = [];
    }
  } else if (fullText && fullTextPattern) {
    const qt = fullTextPattern.trim();
    data = qt
      ? searchLemmaFullText({
          query: qt,
          caseSensitive,
          wholeWord,
          regularExpression,
          limit,
        })
      : [];
  } else {
    const pool = getMysqlPool();
    if (pool) {
      try {
        if (like) {
          if (regex == null || regex === '') {
            if (type === 'missing') {
              data = await queryMissing(pool, limit);
            } else if (type != null) {
              data = await queryByType(pool, type, limit);
            }
          } else {
            data = await queryByLike(pool, regex, caseSensitive, limit);
            if (
              data.length === 0 &&
              !caseSensitive &&
              regex.includes(' ')
            ) {
              const alt = regex.replace(/ /g, '.*');
              data = await queryByRegexp(pool, alt, caseSensitive, limit, !!replacement);
            }
          }
        } else if (regex != null) {
          data = await queryByRegexp(pool, regex, caseSensitive, limit, !!replacement);
        }
      } catch (e) {
        console.warn('[search]', e.message);
        data = [];
      }
    }
  }

  if (replacement && data.length > 0 && regex != null) {
    data = data.filter((item) => moduleFileExists(item.module));
    let pattern = regex;
    if (like) {
      pattern = pattern.replace(/\./g, '\\.');
    } else {
      pattern = pattern.replace(/\\\\/g, '\\');
    }
    const flags = caseSensitive ? '' : 'i';
    const re = new RegExp(pattern, flags);
    data = data.map((item) => ({
      ...item,
      replacement: item.module.replace(re, replacement),
    }));
  }

  return {
    data,
    user: projectUser,
    q: qForVue,
    regularExpression,
    wholeWord,
    caseSensitive,
    fullText: !!fullText,
    lean,
    replacement,
    limit,
    exact,
    similar,
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
  if (q.lean != null && String(q.lean).trim() !== '') return true;
  if (q.fullText === 'on' && q.q != null && String(q.q).trim() !== '') return true;
  return false;
}
