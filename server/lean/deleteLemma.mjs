/**
 * Node port of `php/request/delete/lemma.php`: unlink `Lemma/<module>.lean`, drop `.echo.lean`,
 * optional MySQL `delete from lemma` (same as `delete_from_lemma` in `php/utility.php`).
 */
import fs from 'fs/promises';
import path from 'path';
import { REPO_ROOT, moduleToLeanPath } from './modulePath.mjs';
import { leanEchoPath, getMysqlPool } from './fetchLemmaMysql.mjs';

function normalizePackage(pkg) {
  let s = String(pkg ?? '')
    .replace(/\//g, '.')
    .trim();
  if (s.endsWith('.')) s = s.slice(0, -1);
  return s;
}

/**
 * @param {string} projectUser
 * @param {import('express').Request} req
 * @param {import('express').Response} res
 */
export async function handleDeleteLemma(projectUser, req, res) {
  const body = req.body && typeof req.body === 'object' ? req.body : {};
  const lemma = String(body.lemma ?? '').trim();
  const pkg = normalizePackage(body.package);
  if (!lemma || !pkg) {
    res.status(400).json({ error: 'missing package or lemma' });
    return;
  }

  const module = `${pkg}.${lemma}`;
  const leanPath = moduleToLeanPath(module);
  if (!leanPath) {
    res.status(400).json({ error: 'invalid module' });
    return;
  }

  const lemmaRoot = path.join(REPO_ROOT, 'Lemma');
  const rel = path.relative(path.resolve(lemmaRoot), path.resolve(leanPath));
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) {
    res.status(400).json({ error: 'path outside Lemma/' });
    return;
  }

  try {
    await fs.unlink(leanPath);
  } catch (e) {
    if (/** @type {NodeJS.ErrnoException} */ (e).code === 'ENOENT') {
      res.status(404).json({ error: 'file not found' });
      return;
    }
    throw e;
  }

  try {
    await fs.unlink(leanEchoPath(leanPath));
  } catch {
    /* no sidecar */
  }

  const pool = getMysqlPool();
  if (pool) {
    try {
      await pool.query('DELETE FROM lemma WHERE user = ? AND module = ?', [projectUser, module]);
    } catch (err) {
      console.warn('[delete-lemma mysql]', /** @type {Error} */ (err).message);
    }
  }

  // PHP: `echo std\encode("deleted!");`
  res.json('deleted!');
}
