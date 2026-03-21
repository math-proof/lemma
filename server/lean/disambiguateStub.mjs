/**
 * Same behavior as `php/request/disambiguate.php`: find which top-level `Lemma/<section>/`
 * folder contains the file for a dotted module path (no DB).
 */

import fs from 'fs';
import path from 'path';
import { REPO_ROOT } from './modulePath.mjs';
import { listLemmaTopLevelDirs } from './lemmaSections.mjs';

function existsAsFileOrLean(base) {
  if (fs.existsSync(base)) {
    try {
      return fs.statSync(base).isFile();
    } catch {
      return false;
    }
  }
  const lean = `${base}.lean`;
  return fs.existsSync(lean) && fs.statSync(lean).isFile();
}

function findSectionForSlashPath(sectionDirs, slashPath) {
  const inner = slashPath.replace(/^\//, '');
  const segments = inner.split('/').filter(Boolean);
  if (segments.length === 0) return null;
  for (const section of sectionDirs) {
    const base = path.join(REPO_ROOT, 'Lemma', section, ...segments);
    if (existsAsFileOrLean(base)) return section;
  }
  return null;
}

export function handleDisambiguatePhp(req, res) {
  const moduleInput = (req.body?.module ?? '').toString().trim();
  if (!moduleInput) {
    res.type('text/plain').send('');
    return;
  }

  const sectionDirs = listLemmaTopLevelDirs();
  // PHP: "/" . str_replace('.', '/', $module)
  let slashPath = `/${moduleInput.replace(/\./g, '/')}`;

  let found = findSectionForSlashPath(sectionDirs, slashPath);
  if (found) {
    res.type('text/plain').send(found);
    return;
  }

  // PHP: if (preg_match("#(.+)/[a-z]+$#", $module, $m)) { $module = $m[1]; try_to_die($module); }
  const m = slashPath.match(/^(.+)\/([a-z]+)$/);
  if (m) {
    slashPath = m[1];
    found = findSectionForSlashPath(sectionDirs, slashPath);
    if (found) {
      res.type('text/plain').send(found);
      return;
    }
  }

  res.type('text/plain').send('');
}
