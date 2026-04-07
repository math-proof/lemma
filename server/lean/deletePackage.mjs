/**
 * Node port of `php/request/delete/package.php`: recursively remove `Lemma/<package>.<section>/`
 * and optional MySQL rows for that module prefix (PHP’s `delete_from_lemma` regex call is broken).
 */
import fs from 'fs/promises';
import path from 'path';
import { REPO_ROOT, moduleToLemmaPackageDir } from './modulePath.mjs';
import { getMysqlPool } from './fetchLemmaMysql.mjs';

/**
 * @param {string} projectUser
 * @param {import('express').Request} req
 * @param {import('express').Response} res
 */
export async function handleDeletePackage(projectUser, req, res) {
  const body = req.body && typeof req.body === 'object' ? req.body : {};
  let pkg = String(body.package ?? '')
    .replace(/\//g, '.')
    .trim();
  const section = String(body.section ?? '').trim();
  if (!pkg || !section) {
    res.status(400).json({ error: 'missing package or section' });
    return;
  }
  pkg = pkg.replace(/\.+$/, '');

  const module = `${pkg}.${section}`;
  const dirAbs = moduleToLemmaPackageDir(module);
  if (!dirAbs) {
    res.status(400).json({ error: 'invalid module path' });
    return;
  }

  const lemmaRoot = path.resolve(REPO_ROOT, 'Lemma');
  const rel = path.relative(lemmaRoot, path.resolve(dirAbs));
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) {
    res.status(400).json({ error: 'path outside Lemma/' });
    return;
  }

  try {
    const st = await fs.stat(dirAbs);
    if (!st.isDirectory()) {
      res.status(400).json({ error: 'not a directory' });
      return;
    }
  } catch (e) {
    if (/** @type {NodeJS.ErrnoException} */ (e).code === 'ENOENT') {
      res.status(404).json({ error: 'folder not found' });
      return;
    }
    throw e;
  }

  await fs.rm(dirAbs, { recursive: true, force: true });

  const pool = getMysqlPool();
  if (pool) {
    try {
      await pool.query(
        'DELETE FROM lemma WHERE user = ? AND (module = ? OR module LIKE ?)',
        [projectUser, module, `${module}.%`]
      );
    } catch (err) {
      console.warn('[delete-package mysql]', /** @type {Error} */ (err).message);
    }
  }

  res.json('deleted!');
}
