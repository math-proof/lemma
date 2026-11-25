/**
 * POST `request/fingerprint` — one fingerprint string, fetched when a picture
 * is hovered. `id` is the owning `axiom.lemma` row, selected by module.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';
import { parseFingerprint } from '../leanInvertedIndex.mjs';
import { infixFingerprint } from './infixFingerprint.mjs';

const MODULE_RE = /^[A-Za-z_][A-Za-z0-9_.]*$/;
const SECTIONS = new Set(['given', 'imply', 'proof']);

export async function handleFingerprint(req, res) {
  const module = String(req.body?.module ?? '').trim();
  const section = String(req.body?.section ?? '');
  const lemmaId = Number(req.body?.lemma_id);
  const latexId = Number(req.body?.latex_id);
  if (!MODULE_RE.test(module) || !SECTIONS.has(section) || !Number.isInteger(lemmaId) || lemmaId < 0 || !Number.isInteger(latexId) || latexId < 0) {
    res.status(400).json({ error: 'missing fingerprint key' });
    return;
  }
  const pool = getMysqlPool();
  if (!pool) {
    res.status(503).json({ error: 'MySQL is not configured' });
    return;
  }
  const [rows] = await pool.query(
    `SELECT f.fingerprint AS fingerprint
     FROM fingerprint f
     JOIN lemma l ON l.id = f.id
     WHERE l.module = ? AND f.lemma_id = ? AND f.section = ? AND f.latex_id = ?
     LIMIT 1`,
    [module, lemmaId, section, latexId],
  );
  const fingerprint = rows.length ? infixFingerprint(parseFingerprint(rows[0].fingerprint)) : '';
  res.json({ fingerprint });
}
