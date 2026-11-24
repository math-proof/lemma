/**
 * Port of php/search.php: MySQL (type / like / regex) + filesystem full-text under Lemma/.
 * `?lean=<expression>` (or the search box's Lean checkbox) is an exact
 * subtree-match over lemma conclusions: shortlist via axiom.inverted, then
 * match stored axiom.fingerprint trees (mjs/leanInvertedIndex.mjs).
 * When the exact query has no hit, expanded queries (`∑`/`∏` binder forms,
 * `x²` <-> `x ^ 2`, …) are tried and returned separately as `similar`.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';
import { searchLemmaFullText } from './lemmaFullTextSearch.mjs';
import { moduleToLeanPath, fileExists } from './modulePath.mjs';
import { conclusionNodeOf, sectionFormulaNodes } from '../lemmaPath.mjs';
import { matchAt } from '../leanSubtreeMatch.mjs';

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

/** Search-JSON for one AST node, numbered from a fresh context. */
function nodeSearchJson(node) {
  try {
    return node.toJSON({ leaves: new Map(), binders: [] });
  } catch {
    return null;
  }
}

/**
 * Remove every `\colorbox{color}{…}` background while keeping its content and
 * any foreground color. The parser marks given variables this way for the lemma
 * page; the search result should only show the hit highlight as background.
 */
function stripColorbox(latex) {
  const markers = ["\\colorbox{"];
  let out = "";
  let i = 0;
  while (i < latex.length) {
    let start = -1;
    let marker = "";
    for (const candidate of markers) {
      const at = latex.indexOf(candidate, i);
      if (at >= 0 && (start < 0 || at < start)) {
        start = at;
        marker = candidate;
      }
    }
    if (start < 0) {
      out += latex.slice(i);
      break;
    }
    out += latex.slice(i, start);
    let k = start + marker.length;
    let depth = 1;
    while (k < latex.length && depth > 0) {
      if (latex[k] === "{") depth++;
      else if (latex[k] === "}") depth--;
      k++;
    }
    let brace = k;
    while (brace < latex.length && /\s/.test(latex[brace])) brace++;
    if (latex[brace] !== "{") {
      out += latex.slice(start, k);
      i = k;
      continue;
    }
    const contentStart = brace + 1;
    depth = 1;
    k = contentStart;
    while (k < latex.length && depth > 0) {
      if (latex[k] === "{") depth++;
      else if (latex[k] === "}") depth--;
      k++;
    }
    out += stripColorbox(latex.slice(contentStart, k - 1));
    i = k;
  }
  return out;
}

/** Remove `\tag{…}` / `\tag*{…}` step markers (their content is text-mode, invalid in math). */
function stripTags(latex) {
  let out = "";
  let i = 0;
  while (i < latex.length) {
    if (latex.startsWith("\\tag", i)) {
      let k = i + 4;
      if (latex[k] === "*") k++;
      if (latex[k] === "{") {
        let depth = 1;
        k++;
        while (k < latex.length && depth > 0) {
          if (latex[k] === "{") depth++;
          else if (latex[k] === "}") depth--;
          k++;
        }
        i = k;
        continue;
      }
    }
    out += latex[i];
    i++;
  }
  return out;
}

/** LaTeX of one node with the given-variable background and text-mode `$` removed. */
function nodeLatex(node) {
  try {
    // `$…$` marks Lean text mode, which KaTeX rejects inside math mode.
    return stripColorbox(String(node.toLatex({}) ?? "")).replace(/\$/g, "");
  } catch {
    return "";
  }
}

/**
 * Root-most AST node whose search-JSON matches the query AND whose own LaTeX is
 * a literal substring of `whole`. Wrapper nodes such as `LeanParenthesis` can
 * match structurally but render with extra delimiters, so they are skipped.
 * @returns {{ sub: string } | null}
 */
function findMatchedLatex(node, queryJson, whole) {
  if (node == null || typeof node !== 'object' || queryJson == null) return null;
  const json = nodeSearchJson(node);
  if (json != null && matchAt(queryJson, json)) {
    const sub = nodeLatex(node);
    if (sub && whole.includes(sub)) return { sub };
  }
  for (const child of node.args ?? []) {
    const matched = findMatchedLatex(child, queryJson, whole);
    if (matched) return matched;
  }
  return null;
}

/**
 * Root-most AST node whose search-JSON matches the query, without requiring its
 * LaTeX to occur in a particular rendering. Used for proof steps, whose stored
 * LaTeX (the flattened echo list) is numbered differently from the source steps
 * indexed for search.
 * @returns {{ sub: string } | null}
 */
function findMatchedNode(node, queryJson) {
  if (node == null || typeof node !== 'object' || queryJson == null) return null;
  const json = nodeSearchJson(node);
  if (json != null && matchAt(queryJson, json)) {
    const sub = nodeLatex(node);
    if (sub) return { sub };
  }
  for (const child of node.args ?? []) {
    const matched = findMatchedNode(child, queryJson);
    if (matched) return matched;
  }
  return null;
}

/**
 * LaTeX with layout/colour wrappers removed, used only to compare a stored step
 * with the matched AST node: the page's renderer inserts `\mathord`, `\left`
 * and `\colorbox`, so a literal `includes` cannot decide that they agree.
 */
function normalizeLatex(latex) {
  return stripColorbox(String(latex ?? ''))
    .replace(/\$/g, '')
    .replace(/\\tag\*?\{[\s\S]*?\}/g, '')
    .replace(/\\operatorname\{([^{}]*)\}/g, '$1')
    .replace(/\\(?:color|text|mathrm|mathbf)\{[^{}]*\}/g, '')
    .replace(/\\(?:mathord|left|right|big|Big|bigg|Bigg|,|!|;|quad|qquad|displaystyle|textstyle)/g, '')
    .replace(/\\cdot/g, '*').replace(/\\cos/g, 'cos').replace(/\\sin/g, 'sin')
    .replace(/\\partial/g, 'd').replace(/\\uparrow/g, '^')
    .replace(/\\ /g, '')
    .replace(/[{}\s]/g, '');
}

/**
 * Same reduction as `normalizeLatex`, but keeps, for every emitted character,
 * the `[start, end)` span it came from in the original LaTeX. Needed to place a
 * highlight when the stored rendering and the AST node agree only after the
 * layout wrappers are removed.
 */
function normalizeMapped(latex) {
  const s = stripColorbox(String(latex ?? ''));
  let norm = '';
  const spans = [];
  const emit = (text, start, end) => {
    for (const _ of text) {
      norm += _;
      spans.push([start, end]);
    }
  };
  const skipBraces = (from) => {
    let depth = 1;
    let k = from + 1;
    while (k < s.length && depth > 0) {
      if (s[k] === '{') depth++;
      else if (s[k] === '}') depth--;
      k++;
    }
    return k;
  };
  let i = 0;
  while (i < s.length) {
    const c = s[i];
    if (c === '$' || c === '{' || c === '}' || /\s/.test(c)) { i++; continue; }
    if (c === '\\') {
      if (s.startsWith('\\tag', i)) {
        const star = s[i + 4] === '*' ? 1 : 0;
        if (s[i + 4 + star] === '{') { i = skipBraces(i + 4 + star); continue; }
      }
      if (s.startsWith('\\operatorname{', i)) {
        const open = i + '\\operatorname'.length;
        const k = skipBraces(open);
        for (let j = open + 1; j < k - 1; j++) {
          if (s[j] !== '$' && s[j] !== '{' && s[j] !== '}' && !/\s/.test(s[j])) emit(s[j], j, j + 1);
        }
        i = k;
        continue;
      }
      if (/^\\(?:color|text|mathrm|mathbf)\{/.test(s.slice(i))) {
        i = skipBraces(s.indexOf('{', i));
        continue;
      }
      const layout = /^\\(?:mathord|left|right|big|Big|bigg|Bigg|,|!|;|quad|qquad|displaystyle|textstyle)/.exec(s.slice(i));
      if (layout) { i += layout[0].length; continue; }
      const reps = [['\\cdot', '*'], ['\\cos', 'cos'], ['\\sin', 'sin'], ['\\partial', 'd'], ['\\uparrow', '^']];
      const rep = reps.find(([cmd]) => s.startsWith(cmd, i));
      if (rep) { emit(rep[1], i, i + rep[0].length); i += rep[0].length; continue; }
      if (s.startsWith('\\ ', i)) { i += 2; continue; }
      const generic = /^\\[a-zA-Z]+/.exec(s.slice(i));
      if (generic) { emit(generic[0], i, i + generic[0].length); i += generic[0].length; continue; }
      emit(c, i, i + 1);
      i++;
      continue;
    }
    emit(c, i, i + 1);
    i++;
  }
  return { norm, spans };
}

/**
 * Wrap the stored substring that renders `sub` in the hit highlight, accepting
 * the renderer's differing wrappers. Returns `null` when `sub` is absent or the
 * selected span would leave the LaTeX unbalanced.
 */
function highlightNormalized(stored, sub) {
  const target = normalizeLatex(sub);
  if (target.length < 4) return null;
  const { norm, spans } = normalizeMapped(stored);
  const pos = norm.indexOf(target);
  if (pos < 0) return null;
  let start = spans[pos][0];
  let end = spans[pos + target.length - 1][1];
  const count = (text, re) => (text.match(re) || []).length;
  const body = () => stored.slice(start, end);
  // `net` is the brace balance; `min` is the lowest running balance. A positive
  // `min` protects the inserted group: the span must never close a brace that
  // was opened outside it, or the highlight ends early (e.g. right after the
  // first term of `(cos θ)² + (sin θ)²`).
  const depthInfo = () => {
    let net = 0;
    let min = 0;
    for (const ch of body()) {
      if (ch === '{') net++;
      else if (ch === '}') { net--; if (net < min) min = net; }
    }
    return { net, min };
  };
  // Keep a sizing command with the delimiter that follows it (`\left(`).
  const pre = /\\[a-zA-Z]+\s*$/.exec(stored.slice(0, start));
  if (pre && /^\\(left|middle|big|Big|bigg|Bigg)$/.test(pre[1])) start -= pre[0].length;
  // Widen until `\left`/`\right` and braces balance inside the highlight, so the
  // inserted group never splits a pair or an argument.
  for (let guard = 0; guard < 12; guard++) {
    let changed = false;
    while (count(body(), /\\right/g) > count(body(), /\\left/g)) {
      const at = stored.lastIndexOf('\\left', start - 1);
      if (at < 0) break;
      start = at;
      changed = true;
    }
    while (count(body(), /\\left/g) > count(body(), /\\right/g)) {
      const at = stored.indexOf('\\right', end);
      if (at < 0) break;
      end = at + '\\right'.length;
      while (end < stored.length && /\s/.test(stored[end])) end++;
      if (end < stored.length && !/[a-zA-Z]/.test(stored[end])) end++;
      changed = true;
    }
    while (depthInfo().min < 0) {
      const at = stored.lastIndexOf('{', start - 1);
      if (at < 0) break;
      start = at;
      changed = true;
    }
    while (depthInfo().net > 0) {
      const at = stored.indexOf('}', end);
      if (at < 0) break;
      end = at + 1;
      changed = true;
    }
    if (!changed) break;
  }
  if (depthInfo().net !== 0 || depthInfo().min < 0) return null;
  return stored.slice(0, start) + `\\htmlClass{lean-hit}{${body()}}` + stored.slice(end);
}

/**
 * Conclusion LaTeX for one hit, with the matched sub-structure wrapped in
 * `\htmlClass{lean-hit}{…}` when the query matches a proper child. Returns
 * `{ latex: null }` when the module has no readable source.
 */
function latexForModule(module, queryJson) {
  const abs = moduleToLeanPath(module);
  if (abs == null || !fileExists(abs)) return { latex: null };
  try {
    const node = conclusionNodeOf(abs);
    const whole = nodeLatex(node);
    if (!whole) return { latex: null };
    const matched = findMatchedLatex(node, queryJson, whole);
    if (matched != null) {
      const { sub } = matched;
      return {
        latex: whole.replace(sub, () => `\\htmlClass{lean-hit}{${sub}}`),
        highlighted: true,
      };
    }
    return { latex: whole, highlighted: false };
  } catch {
    return { latex: null };
  }
}

/**
 * LaTeX of the section formula that matched (given / proof), instead of the
 * conclusion, with the matched sub-structure highlighted when possible.
 */
function sectionLatex(module, { section, latexId }, queryJson) {
  const abs = moduleToLeanPath(module);
  if (abs == null || !fileExists(abs)) return { latex: null };
  try {
    const items = sectionFormulaNodes(abs, section, latexId);
    for (const { node } of items) {
      const whole = nodeLatex(node);
      if (!whole) continue;
      const matched = findMatchedLatex(node, queryJson, whole);
      if (!matched) continue;
      const { sub } = matched;
      return {
        latex: whole.replace(sub, () => `\\htmlClass{lean-hit}{${sub}}`),
        highlighted: true,
      };
    }
    const whole = items.map(({ node }) => nodeLatex(node)).filter(Boolean).join('\\quad ');
    return whole ? { latex: whole, highlighted: false } : { latex: null };
  } catch {
    return { latex: null };
  }
}

/**
 * Proof LaTeX for one hit. The search index numbers proof steps by top-level
 * source statement, while the lemma page renders `lemma.proof.by[i]`, a flattened
 * echo list — the two indices drift, so `steps[latexId]` is a different step.
 * Instead, locate the matched formula and show the stored step that renders it;
 * when no stored step contains it (e.g. a `calc` line the page keeps as code
 * only), show the matched formula itself rather than an unrelated step.
 * @param {string[]} steps stored, colour/tag-stripped `proof.by[i].latex`
 */
function proofLatex(module, { latexId }, queryJson, steps) {
  const abs = moduleToLeanPath(module);
  if (abs == null || !fileExists(abs)) return { latex: null, highlighted: false };
  try {
    const items = sectionFormulaNodes(abs, 'proof', latexId);
    let matched = null;
    for (const { node } of items) {
      matched = findMatchedNode(node, queryJson);
      if (matched) break;
    }
    if (!matched) return { latex: null, highlighted: false };
    const { sub } = matched;
    // Prefer the step the lemma page renders below the code (same formula).
    for (let i = 0; i < steps.length; i++) {
      if (steps[i] && steps[i].includes(sub)) {
        return {
          latex: steps[i].replace(sub, () => `\\htmlClass{lean-hit}{${sub}}`),
          highlighted: true,
          latexId: i,
        };
      }
    }
    // Same formula modulo the renderer's wrappers: highlight the stored span.
    for (let i = 0; i < steps.length; i++) {
      if (!steps[i]) continue;
      const highlighted = highlightNormalized(steps[i], sub);
      if (highlighted) return { latex: highlighted, highlighted: true, latexId: i };
    }
    return { latex: `\\htmlClass{lean-hit}{${sub}}`, highlighted: true };
  } catch {
    return { latex: null, highlighted: false };
  }
}

/** Stripped `proof.by[i].latex` lists keyed by module, for `proofLatex`. */
const storedProofCache = new Map();

/** Every proof-step LaTeX the lemma page can render for `module`. */
async function storedProofSteps(pool, module) {
  if (!pool) return [];
  let steps = storedProofCache.get(module);
  if (steps === undefined) {
    let row = null;
    try {
      const [rows] = await pool.query(
        'SELECT lemma FROM axiom.lemma WHERE module = ? ORDER BY id DESC LIMIT 1', [module]);
      row = Array.isArray(rows) && rows.length ? rows[0].lemma : null;
    } catch {
      row = null;
    }
    const lemma = Array.isArray(row) ? row[0] : row;
    const proof = lemma?.proof;
    const list = Array.isArray(proof?.by) ? proof.by
      : Array.isArray(proof?.calc) ? proof.calc
        : Array.isArray(proof) ? proof : [];
    steps = list.map((step) => {
      const latex = step?.latex;
      return typeof latex === 'string' && latex
        ? stripTags(stripColorbox(latex)).replace(/\$/g, '')
        : '';
    });
    storedProofCache.set(module, steps);
  }
  return steps;
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {number} limit
 */
async function queryMissing(pool, limit, offset) {
  const sql = `
SELECT module
FROM lemma
WHERE json_length(imports) > 0 AND json_length(lemma) = 0
LIMIT ? OFFSET ?`;
  const [rows] = await pool.query(sql, [limit + 1, offset]);
  return pageRows(rows, limit);
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} type
 * @param {number} limit
 */
async function queryByType(pool, type, limit, offset) {
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
LIMIT ? OFFSET ?`;
  const [rows] = await pool.query(sql, [type, limit + 1, offset]);
  return pageRows(rows, limit);
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} keyword
 * @param {boolean} binary
 * @param {number} limit
 */
async function queryByLike(pool, keyword, binary, limit, offset) {
  const esc = String(keyword).replace(/\\/g, '\\\\').replace(/_/g, '\\_').replace(/%/g, '\\%');
  const pattern = `%${esc}%`;
  const sql = binary
    ? 'SELECT module FROM lemma WHERE module LIKE BINARY ? LIMIT ? OFFSET ?'
    : 'SELECT module FROM lemma WHERE module LIKE ? LIMIT ? OFFSET ?';
  const [rows] = await pool.query(sql, [pattern, limit + 1, offset]);
  return pageRows(rows, limit);
}

/**
 * @param {import('mysql2/promise').Pool} pool
 * @param {string} pattern
 * @param {boolean} binary
 * @param {number} limit
 * @param {boolean} requireImports
 */
async function queryByRegexp(pool, pattern, binary, limit, requireImports, offset) {
  let where = binary
    ? 'module REGEXP ? COLLATE utf8mb4_bin'
    : 'module REGEXP ?';
  if (requireImports) where += ' AND json_length(imports) > 0';
  const sql = `SELECT module FROM lemma WHERE ${where} LIMIT ? OFFSET ?`;
  const [rows] = await pool.query(sql, [pattern, limit + 1, offset]);
  return pageRows(rows, limit);
}

/** One extra row means another page exists. */
function pageRows(rows, limit) {
  const list = Array.isArray(rows) ? rows : [];
  const more = list.length > limit;
  return { rows: more ? list.slice(0, limit) : list, more };
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

  const SECTION_NAMES = new Set(['given', 'imply', 'proof']);
  const requestedSections = String(dict.section ?? '')
    .split(',')
    .map((name) => name.trim())
    .filter((name) => SECTION_NAMES.has(name));
  const sections = requestedSections.length ? requestedSections : ['imply'];

  const caseSensitive = hasKey(dict, 'caseSensitive');
  const wholeWord = hasKey(dict, 'wholeWord');
  const regularExpression = hasKey(dict, 'regularExpression');
  const replacement = dict.replacement != null && String(dict.replacement) !== '' ? String(dict.replacement) : null;
  const limit = Math.min(1000, Math.max(1, Number(dict.limit) || 100));
  const start = Math.max(0, Number(dict.start) || 0);
  let more = false;

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
      const result = await searchLeanSimilar(lean, { limit, offset: start, pool, sections });
      const queryJson = result.query?.json ?? null;
      const enrich = async (hit) => {
        // A similarity hit matched an expanded query (`a²+b²` → `a^2+b^2`), so
        // rendering must look for the tree that actually matched this hit.
        const { queryJson: hitQuery, ...base } = hit;
        const hitJson = hitQuery ?? queryJson;
        if (hit.section && hit.section !== 'imply') {
          if (hit.section === 'proof') {
            const steps = await storedProofSteps(pool, hit.module);
            return { ...base, ...proofLatex(hit.module, hit, hitJson, steps) };
          }
          return { ...base, ...sectionLatex(hit.module, hit, hitJson) };
        }
        return { ...base, ...latexForModule(hit.module, hitJson) };
      };
      exact = await Promise.all(result.exact.map((hit) => enrich({ ...hit, match: 'exact' })));
      similar = await Promise.all(result.similar.map((hit) => enrich({ ...hit, match: 'similar' })));
      data = (result.exactTotal ?? 0) > 0 ? exact : similar;
      more = !!result.more;
    } catch (e) {
      console.warn('[lean-search]', e.message);
      data = [];
    }
  } else if (fullText && fullTextPattern) {
    const qt = fullTextPattern.trim();
    if (qt) {
      const found = searchLemmaFullText({
        query: qt,
        caseSensitive,
        wholeWord,
        regularExpression,
        limit,
        offset: start,
      });
      data = found.results;
      more = found.more;
    }
  } else {
    const pool = getMysqlPool();
    if (pool) {
      try {
        const assignPage = (page) => {
          data = page.rows;
          more = page.more;
        };
        if (like) {
          if (regex == null || regex === '') {
            if (type === 'missing') {
              assignPage(await queryMissing(pool, limit, start));
            } else if (type != null) {
              assignPage(await queryByType(pool, type, limit, start));
            }
          } else {
            const liked = await queryByLike(pool, regex, caseSensitive, limit, start);
            if (
              start === 0 &&
              liked.rows.length === 0 &&
              !caseSensitive &&
              regex.includes(' ')
            ) {
              const alt = regex.replace(/ /g, '.*');
              assignPage(await queryByRegexp(pool, alt, caseSensitive, limit, !!replacement, start));
            } else {
              assignPage(liked);
            }
          }
        } else if (regex != null) {
          assignPage(await queryByRegexp(pool, regex, caseSensitive, limit, !!replacement, start));
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
    section: sections.join(','),
    replacement,
    limit,
    start,
    more,
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
