/**
 * Node port of `php/request/rename.php` (POST `old`, `new` as dotted modules under `Lemma/`).
 * Runs `sh/rename.sh` (Linux) or `ps1/rename.ps1` (Windows), then optional MySQL `update_axiom`-style updates.
 * The `package` + folder branch from PHP is not implemented here (legacy `smallIcon.vue` payload).
 */
import path from 'path';
import { spawnSync } from 'node:child_process';
import os from 'os';
import { REPO_ROOT, moduleToLeanPath, fileExists } from './modulePath.mjs';
import { getMysqlPool } from './fetchLemmaMysql.mjs';

/** @param {string} m */
function isSafeLemmaModule(m) {
  if (!m || typeof m !== 'string') return false;
  if (m.includes('..') || m.includes('/') || m.includes('\\') || m.includes('#')) return false;
  const parts = m.split('.').filter(Boolean);
  if (parts.length === 0) return false;
  return parts.every((p) => /^[A-Za-z][A-Za-z0-9_'!?₀-₉]*$/.test(p));
}

/**
 * @param {string} projectUser
 * @param {string} oldModule
 * @param {string} newModule
 */
async function updateAxiomModuleRow(projectUser, oldModule, newModule) {
  const pool = getMysqlPool();
  if (!pool) return;
  const lemmaOld = `Lemma.${oldModule}`;
  const lemmaNew = `Lemma.${newModule}`;
  try {
    await pool.query('UPDATE lemma SET module = ? WHERE user = ? AND module = ?', [
      newModule,
      projectUser,
      oldModule,
    ]);
    await pool.query(
      `UPDATE lemma SET imports = JSON_REPLACE(
        imports,
        JSON_UNQUOTE(JSON_SEARCH(imports, 'one', ?)),
        ?
      ) WHERE user = ? AND JSON_CONTAINS(imports, JSON_QUOTE(?))`,
      [lemmaOld, lemmaNew, projectUser, lemmaOld]
    );
  } catch (e) {
    console.warn('[rename mysql]', /** @type {Error} */ (e).message);
  }
}

/**
 * @param {string} old
 * @param {string} new_
 */
function runRenameShell(old, new_) {
  const cwd = REPO_ROOT;
  if (os.platform() === 'win32') {
    const ps1 = path.join(REPO_ROOT, 'ps1', 'rename.ps1');
    return spawnSync(
      'powershell.exe',
      ['-NoProfile', '-ExecutionPolicy', 'Bypass', '-File', ps1, '-src', old, '-dst', new_],
      {
        cwd,
        encoding: 'utf-8',
        maxBuffer: 50 * 1024 * 1024,
        /** Avoid a flashing console window when PowerShell runs the rename script (Windows). */
        windowsHide: true,
      }
    );
  }
  return spawnSync('bash', ['sh/rename.sh', old, new_], {
    cwd,
    encoding: 'utf-8',
    maxBuffer: 50 * 1024 * 1024,
    windowsHide: true,
  });
}

/**
 * @param {string} projectUser
 * @param {import('express').Request} req
 * @param {import('express').Response} res
 */
export async function handleRenameLemma(projectUser, req, res) {
  const body = req.body && typeof req.body === 'object' ? req.body : {};
  const pkg = body.package != null && String(body.package).trim() !== '' ? String(body.package) : null;

  if (pkg != null) {
    res.status(501).json({
      error:
        'Node server: package-scoped rename (POST package + old/new) is not implemented. Use dotted `old` and `new` only, or run PHP rename.',
    });
    return;
  }

  const old = String(body.old ?? '')
    .trim()
    .replace(/\//g, '.');
  const new_ = String(body.new ?? '')
    .trim()
    .replace(/\//g, '.');

  if (!old || !new_) {
    res.status(400).json({ error: 'missing old or new' });
    return;
  }
  if (old === new_) {
    res.status(200).json('renamed!');
    return;
  }
  if (!isSafeLemmaModule(old) || !isSafeLemmaModule(new_)) {
    res.status(400).json({ error: 'invalid module' });
    return;
  }

  const oldAbs = moduleToLeanPath(old);
  const newAbs = moduleToLeanPath(new_);
  if (!oldAbs || !newAbs) {
    res.status(400).json({ error: 'invalid module path' });
    return;
  }

  const lemmaRoot = path.join(REPO_ROOT, 'Lemma');
  const relOld = path.relative(path.resolve(lemmaRoot), path.resolve(oldAbs));
  const relNew = path.relative(path.resolve(lemmaRoot), path.resolve(newAbs));
  if (!relOld || relOld.startsWith('..') || path.isAbsolute(relOld)) {
    res.status(400).json({ error: 'old path outside Lemma/' });
    return;
  }
  if (!relNew || relNew.startsWith('..') || path.isAbsolute(relNew)) {
    res.status(400).json({ error: 'new path outside Lemma/' });
    return;
  }

  if (fileExists(newAbs)) {
    res.status(409).type('text/plain; charset=utf-8').send(`${newAbs} already exists`);
    return;
  }
  if (!fileExists(oldAbs)) {
    res.status(404).type('text/plain; charset=utf-8').send(`source ${oldAbs} does not exist`);
    return;
  }

  const sh = runRenameShell(old, new_);
  if (sh.status !== 0) {
    const errOut = [sh.stderr, sh.stdout].filter(Boolean).join('\n').trim();
    console.error('[rename]', errOut || `exit ${sh.status}`);
    res.status(500).type('text/plain; charset=utf-8').send(errOut || `rename script exited with code ${sh.status}`);
    return;
  }

  await updateAxiomModuleRow(projectUser, old, new_);

  /** Same as PHP `echo std\\encode("renamed!");` — JSON string for axios. */
  res.status(200).json('renamed!');
}
