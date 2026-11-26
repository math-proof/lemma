/**
 * POST `request/rebuild_fingerprint` — replace one lemma's
 * `axiom.inverted` postings and `axiom.fingerprint` trees from its Lean source.
 * Same write as `node mjs/leanInvertedIndex.mjs --refresh-module`.
 *
 * The lemma page does not call this after Echo. `request/echo` already stored
 * the proof fingerprints from `expr.toJson` (paired with the `expr.toLatex`
 * pictures), and a source rebuild cannot reproduce those goals — so it keeps
 * the existing `proof` rows instead of replacing them.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';
import { refreshInvertedForModule } from '../leanInvertedIndex.mjs';
import { isValidModuleName } from './modulePath.mjs';

export async function handleRebuildFingerprint(req, res) {
  const module = String(req.body?.module ?? '').trim();
  if (!isValidModuleName(module)) {
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
