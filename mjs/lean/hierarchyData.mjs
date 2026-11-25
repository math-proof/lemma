/**
 * Callee/caller import graphs for `hierarchy.vue`, including cycle tracebacks.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';
import { commutativeImportAlias } from './moduleResolve.mjs';

/**
 * @param {string} module
 * @param {boolean} reverse true = who imports this module (callee view); false = this module's imports (caller view)
 */
async function selectHierarchyFromDb(module, reverse) {
  const pool = getMysqlPool();
  if (!pool) return [];

  if (reverse) {
    const alt = commutativeImportAlias(module);
    const [rows] = await pool.query(
      alt
        ? `SELECT DISTINCT module FROM lemma
           WHERE (
             JSON_CONTAINS(imports, JSON_QUOTE(CONCAT('Lemma.', ?)), '$')
             OR JSON_CONTAINS(imports, JSON_QUOTE(CONCAT('Lemma.', ?)), '$')
           )`
        : `SELECT module FROM lemma
           WHERE JSON_CONTAINS(imports, JSON_QUOTE(CONCAT('Lemma.', ?)), '$')`,
      alt ? [module, alt] : [module]
    );
    if (!Array.isArray(rows)) return [];
    return rows.map((/** @type {{ module: string }} */ r) => r.module);
  }

  const [rows] = await pool.query(
    'SELECT imports FROM lemma WHERE module = ? LIMIT 1',
    [module]
  );
  if (!Array.isArray(rows) || rows.length === 0) return [];
  let imports = rows[0].imports;
  if (typeof imports === 'string') {
    try {
      imports = JSON.parse(imports);
    } catch {
      return [];
    }
  }
  if (!Array.isArray(imports)) return [];

  /** @type {string[]} */
  const out = [];
  for (const result of imports) {
    if (typeof result !== 'string') continue;
    const m = /^Lemma\.(.+)/.exec(result);
    if (m && m[1] !== 'Basic') out.push(m[1]);
  }
  return out;
}

/**
 * Adjacency list: node -> child modules.
 * @param {string} startNode
 * @param {boolean} reverse
 * @returns {Promise<Record<string, string[]>>}
 */
export async function establishHierarchyGraph(startNode, reverse) {
  /** @type {Record<string, string[]>} */
  const G = {};
  const processed = new Set();
  /** @type {string[]} */
  const queue = [startNode];
  const cache = new Map();

  while (queue.length > 0) {
    const node = queue.shift();
    if (!node || processed.has(node)) continue;
    processed.add(node);

    const cacheKey = `${reverse ? 'r' : 'f'}:${node}`;
    let children = cache.get(cacheKey);
    if (!children) {
      children = await selectHierarchyFromDb(node, reverse);
      cache.set(cacheKey, children);
    }

    for (const child of children) {
      queue.push(child);
      if (!G[node]) G[node] = [];
      if (!G[node].includes(child)) G[node].push(child);
    }
  }

  return G;
}

/**
 * @param {Record<string, string[]>} graph
 * @param {string} startKey
 * @param {string[]} parent path mutated while walking
 */
export function detectCycleTraceback(graph, startKey, parent) {
  const permanent = new Set();
  const temporary = new Set();

  function visitAndTraceback(n) {
    if (permanent.has(n)) return null;
    if (temporary.has(n)) return n;

    const children = graph[n];
    if (children != null && Array.isArray(children) && children.length > 0) {
      temporary.add(n);
      for (const m of children) {
        const node = visitAndTraceback(m);
        if (node != null) {
          parent.push(m);
          return node;
        }
      }
      temporary.delete(n);
    }

    permanent.add(n);
    return null;
  }

  visitAndTraceback(startKey);
}

/**
 * @param {string[]} parent
 * @param {string} module
 * @returns {string[] | null}
 */
export function buildHierarchyTraceback(parent, module) {
  if (!parent || parent.length === 0) return null;
  const cyclicProof = parent[0];
  let i = 1;
  for (; i < parent.length; i++) {
    if (parent[i] === cyclicProof) break;
  }
  const extended = [...parent, module];
  /** @type {string[]} */
  const traceback = [];
  for (let j = extended.length - 1; j >= i; j--) {
    traceback.push(extended[j]);
  }
  return traceback;
}
