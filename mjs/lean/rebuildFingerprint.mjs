/**
 * POST `request/rebuild_fingerprint` — replace one lemma's
 * `axiom.inverted` postings and `axiom.fingerprint` trees from its Lean source.
 * Same write as `node mjs/leanInvertedIndex.mjs --refresh-module`.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';
import { refreshInvertedForModule } from '../leanInvertedIndex.mjs';

const MODULE_RE = /^[A-Za-z_][A-Za-z0-9_.]*$/;

export async function handleRebuildFingerprint(req, res) {
  const module = String(req.body?.module ?? '').trim();
  if (!MODULE_RE.test(module)) {
    res.status(400).json({ error: 'missing module' });
    return;
  }
  const pool = getMysqlPool();
  if (!pool) {
    res.status(503).json({ error: 'MySQL is not configured' });
    return;
  }
  try {
    const result = await refreshInvertedForModule(pool, module);
    res.json(result);
  } catch (e) {
    const message = String(e?.message || e);
    const status = message.startsWith('No Lean source') ? 404 : 500;
    res.status(status).json({ error: message });
  }
}
