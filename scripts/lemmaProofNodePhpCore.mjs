/**
 * Shared fetch + compare for Node vs PHP lemma pages (`lemma[].proof`).
 * Used by compare-lemma-proof-node-php.mjs and scan-lemma-proof-node-php.mjs.
 */
import process from 'process';

/** @returns {{ nodeBase: string, phpBase: string }} */
export function lemmaProofCompareBases() {
  const nodeBase = (
    process.env.LEAN_NODE_LEMMA_BASE || 'http://127.0.0.1/lean/'
  ).replace(/\/?$/, '/');
  const phpBase = (
    process.env.LEAN_PHP_LEMMA_BASE || 'http://127.0.0.1:8080/lean.php/'
  ).replace(/\/?$/, '/');
  return { nodeBase, phpBase };
}

/** @param {string} base @param {string} module */
export function lemmaUrl(base, module) {
  const u = new URL(base);
  u.searchParams.set('module', module);
  return u.href;
}

async function fetchText(url) {
  const res = await fetch(url, { redirect: 'follow' });
  if (!res.ok) {
    throw new Error(`${res.status} ${res.statusText} for ${url}`);
  }
  return res.text();
}

/**
 * @param {string} html
 * @returns {Record<string, unknown>}
 */
export function extractPayload(html) {
  const needle = "createApp('render', ";
  const i = html.indexOf(needle);
  if (i < 0) {
    throw new Error('createApp(\'render\', …) not found in HTML');
  }
  const start = i + needle.length;
  if (html[start] !== '{') {
    throw new Error('expected JSON object after createApp');
  }
  let depth = 0;
  let inStr = false;
  let esc = false;
  let q = '';
  for (let j = start; j < html.length; j++) {
    const c = html[j];
    if (inStr) {
      if (esc) {
        esc = false;
        continue;
      }
      if (c === '\\') {
        esc = true;
        continue;
      }
      if (c === q) {
        inStr = false;
        q = '';
        continue;
      }
      continue;
    }
    if (c === '"' || c === "'") {
      inStr = true;
      q = c;
      continue;
    }
    if (c === '{') depth++;
    if (c === '}') {
      depth--;
      if (depth === 0) {
        return /** @type {Record<string, unknown>} */ (
          JSON.parse(html.slice(start, j + 1))
        );
      }
    }
  }
  throw new Error('unbalanced braces in embedded JSON');
}

/** @param {unknown} a @param {unknown} b */
export function deepEqualProofPayload(a, b) {
  if (a === b) return true;
  if (a == null || b == null) return a === b;
  if (typeof a !== typeof b) return false;
  if (Array.isArray(a)) {
    if (!Array.isArray(b) || a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!deepEqualProofPayload(a[i], b[i])) return false;
    }
    return true;
  }
  if (typeof a === 'object') {
    const oa = /** @type {Record<string, unknown>} */ (a);
    const ob = /** @type {Record<string, unknown>} */ (b);
    const ka = Object.keys(oa).sort();
    const kb = Object.keys(ob).sort();
    if (ka.length !== kb.length || ka.join() !== kb.join()) return false;
    for (const k of ka) {
      if (!deepEqualProofPayload(oa[k], ob[k])) return false;
    }
    return true;
  }
  return false;
}

/**
 * @param {unknown} payload
 * @returns {unknown[]}
 */
export function proofListFromPayload(payload) {
  const lemma = payload?.lemma;
  if (!Array.isArray(lemma)) {
    throw new Error('payload.lemma is not an array');
  }
  return lemma.map((L) => {
    if (L == null || typeof L !== 'object' || !('proof' in L)) {
      throw new Error('lemma entry missing .proof');
    }
    return /** @type {{ proof: unknown }} */ (L).proof;
  });
}

/**
 * Compare only `proof.by[].lean` between two proof objects.
 * @returns {{ ok: true } | { ok: false, step: number, nodeLean: unknown, phpLean: unknown, reason?: string }}
 */
export function compareProofByLeanOnly(nodeProof, phpProof) {
  const nb = /** @type {{ by?: unknown }} */ (nodeProof)?.by;
  const pb = /** @type {{ by?: unknown }} */ (phpProof)?.by;
  if (!Array.isArray(nb) || !Array.isArray(pb)) {
    return {
      ok: false,
      step: -1,
      nodeLean: undefined,
      phpLean: undefined,
      reason: 'proof.by missing or not an array on one side',
    };
  }
  if (nb.length !== pb.length) {
    return {
      ok: false,
      step: -1,
      nodeLean: nb.length,
      phpLean: pb.length,
      reason: `proof.by length node ${nb.length} vs php ${pb.length}`,
    };
  }
  for (let s = 0; s < nb.length; s++) {
    const ln = /** @type {{ lean?: unknown }} */ (nb[s])?.lean;
    const lp = /** @type {{ lean?: unknown }} */ (pb[s])?.lean;
    if (ln !== lp) {
      return { ok: false, step: s, nodeLean: ln, phpLean: lp };
    }
  }
  return { ok: true };
}

/** @param {unknown} stepNode @param {unknown} stepPhp */
function proofStepMismatchDescription(stepNode, stepPhp) {
  const sn = /** @type {{ lean?: unknown, latex?: unknown }} */ (stepNode);
  const sp = /** @type {{ lean?: unknown, latex?: unknown }} */ (stepPhp);
  const leanSame = sn?.lean === sp?.lean;
  const latexSame =
    JSON.stringify(sn?.latex) === JSON.stringify(sp?.latex);
  if (!leanSame) {
    return `lean node=${JSON.stringify(sn?.lean)} php=${JSON.stringify(sp?.lean)}`;
  }
  if (!latexSame) {
    return 'LaTeX differs (lean matches)';
  }
  return 'step differs';
}

/**
 * @param {string} moduleName
 * @param {{ nodeBase?: string, phpBase?: string, includeLatex?: boolean }} [bases]
 * @returns {Promise<{ code: 0 | 1 | 2, moduleName: string, nodeUrl: string, phpUrl: string, message?: string }>}
 */
export async function compareLemmaProof(moduleName, bases) {
  const merged = bases ?? lemmaProofCompareBases();
  const { nodeBase, phpBase } = merged;
  const includeLatex =
    typeof merged.includeLatex === 'boolean'
      ? merged.includeLatex
      : process.env.LEAN_PROOF_COMPARE_INCLUDE_LATEX === '1';
  const nodeUrl = lemmaUrl(nodeBase, moduleName);
  const phpUrl = lemmaUrl(phpBase, moduleName);

  let nodeHtml;
  let phpHtml;
  try {
    [nodeHtml, phpHtml] = await Promise.all([
      fetchText(nodeUrl),
      fetchText(phpUrl),
    ]);
  } catch (e) {
    const msg = String(/** @type {Error} */ (e).message || e);
    return {
      code: 2,
      moduleName,
      nodeUrl,
      phpUrl,
      message: msg,
    };
  }

  let nodePayload;
  let phpPayload;
  try {
    nodePayload = extractPayload(nodeHtml);
    phpPayload = extractPayload(phpHtml);
  } catch (e) {
    const msg = String(/** @type {Error} */ (e).message || e);
    return {
      code: 2,
      moduleName,
      nodeUrl,
      phpUrl,
      message: `Parse: ${msg}`,
    };
  }

  let nodeProofs;
  let phpProofs;
  try {
    nodeProofs = proofListFromPayload(nodePayload);
    phpProofs = proofListFromPayload(phpPayload);
  } catch (e) {
    const msg = String(/** @type {Error} */ (e).message || e);
    return {
      code: 2,
      moduleName,
      nodeUrl,
      phpUrl,
      message: msg,
    };
  }

  if (nodeProofs.length !== phpProofs.length) {
    return {
      code: 1,
      moduleName,
      nodeUrl,
      phpUrl,
      message: `Different lemma count: node ${nodeProofs.length} vs php ${phpProofs.length}`,
    };
  }

  for (let i = 0; i < nodeProofs.length; i++) {
    if (includeLatex) {
      if (!deepEqualProofPayload(nodeProofs[i], phpProofs[i])) {
        let detail = `Proof differs at lemma[${i}]`;
        const nb = /** @type {{ by?: unknown }} */ (nodeProofs[i])?.by;
        const pb = /** @type {{ by?: unknown }} */ (phpProofs[i])?.by;
        if (Array.isArray(nb) && Array.isArray(pb) && nb.length === pb.length) {
          for (let s = 0; s < nb.length; s++) {
            if (!deepEqualProofPayload(nb[s], pb[s])) {
              detail += ` proof.by[${s}]: ${proofStepMismatchDescription(nb[s], pb[s])}`;
              break;
            }
          }
        }
        return {
          code: 1,
          moduleName,
          nodeUrl,
          phpUrl,
          message: detail,
        };
      }
    } else {
      const leanCmp = compareProofByLeanOnly(nodeProofs[i], phpProofs[i]);
      if (!leanCmp.ok) {
        let msg = `Lean differs at lemma[${i}]`;
        if (leanCmp.reason) {
          msg += `: ${leanCmp.reason}`;
        } else if (leanCmp.step >= 0) {
          msg += ` proof.by[${leanCmp.step}]: node=${JSON.stringify(leanCmp.nodeLean)} php=${JSON.stringify(leanCmp.phpLean)}`;
        }
        return {
          code: 1,
          moduleName,
          nodeUrl,
          phpUrl,
          message: msg,
        };
      }
    }
  }

  return { code: 0, moduleName, nodeUrl, phpUrl };
}
