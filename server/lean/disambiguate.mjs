/**
 * Legacy path `php/request/disambiguate.php`: find which top-level `Lemma/<section>/`
 * folder contains the file for a dotted module path (no DB).
 */

import fs from 'fs';
import path from 'path';
import { REPO_ROOT } from './modulePath.mjs';
import { listLemmaTopLevelDirs } from './lemmaSections.mjs';

function existsAsFileOrLean(base) {
  // A namespace directory (`Set/In_Ico/`) must not hide the sibling module file `Set/In_Ico.lean`.
  const lean = `${base}.lean`;
  if (fs.existsSync(lean)) {
    try {
      if (fs.statSync(lean).isFile()) return true;
    } catch {
      /* keep checking the unsuffixed path */
    }
  }
  if (!fs.existsSync(base)) return false;
  try {
    return fs.statSync(base).isFile();
  } catch {
    return false;
  }
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

/**
 * @param {string} moduleInput dotted path under a section (`GradV.eq.….In_Ico`)
 * @param {string} [onlySection] when set, succeed only if the file is in that section
 * @returns {string} section name, or `''`
 */
export function disambiguateModule(moduleInput, onlySection = '') {
  const moduleName = (moduleInput ?? '').toString().trim();
  if (!moduleName) return '';

  let sectionDirs = listLemmaTopLevelDirs();
  const only = (onlySection ?? '').toString().trim();
  if (only) {
    if (!sectionDirs.includes(only)) return '';
    sectionDirs = [only];
  }

  // PHP: "/" . str_replace('.', '/', $module)
  let slashPath = `/${moduleName.replace(/\./g, '/')}`;

  let found = findSectionForSlashPath(sectionDirs, slashPath);
  if (found) return found;

  // PHP: if (preg_match("#(.+)/[a-z]+$#", $module, $m)) { $module = $m[1]; try_to_die($module); }
  const m = slashPath.match(/^(.+)\/([a-z]+)$/);
  if (m) {
    found = findSectionForSlashPath(sectionDirs, m[1]);
    if (found) return found;
  }
  return '';
}

export function handleDisambiguate(req, res) {
  const found = disambiguateModule(req.body?.module, req.body?.section);
  res.type('text/plain').send(found);
}
