/**
 * Recursive `.lean` search under `Lemma/<folderModule>/` (or all of `Lemma/` when folder is empty).
 */
import fs from 'fs';
import path from 'path';
import { REPO_ROOT, moduleToLemmaPackageDir, leanPathToModule } from './modulePath.mjs';

export const FOLDER_LEAN_SEARCH_MAX_HITS = 2000;

/**
 * @param {string} folderModuleDotted dotted path, no trailing dots; `''` = whole `Lemma/`
 * @param {string} query
 * @returns {{ module: string, name: string, mtimeMs: number, size: number }[]}
 */
export function searchLeanFilesRecursiveUnderFolder(folderModuleDotted, query) {
  const needle = String(query ?? '').trim().toLowerCase();
  if (!needle) return [];

  const lemmaRoot = path.join(REPO_ROOT, 'Lemma');
  let root;
  const m = String(folderModuleDotted ?? '')
    .trim()
    .replace(/\//g, '.')
    .replace(/\.+$/, '');
  if (!m) {
    root = lemmaRoot;
  } else {
    const resolved = moduleToLemmaPackageDir(m);
    if (!resolved) return [];
    root = resolved;
  }

  try {
    if (!fs.existsSync(root) || !fs.statSync(root).isDirectory()) return [];
  } catch {
    return [];
  }

  /** @type {{ module: string, name: string, mtimeMs: number, size: number }[]} */
  const hits = [];

  function walk(dir) {
    if (hits.length >= FOLDER_LEAN_SEARCH_MAX_HITS) return;
    let entries;
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const e of entries) {
      if (hits.length >= FOLDER_LEAN_SEARCH_MAX_HITS) return;
      const full = path.join(dir, e.name);
      if (e.isDirectory()) {
        walk(full);
      } else if (e.name.endsWith('.lean') && !e.name.endsWith('.echo.lean')) {
        const mod = leanPathToModule(full);
        if (!mod) continue;
        const base = e.name.slice(0, -'.lean'.length);
        if (base.toLowerCase().includes(needle) || mod.toLowerCase().includes(needle)) {
          let st;
          try {
            st = fs.statSync(full);
          } catch {
            continue;
          }
          hits.push({
            module: mod,
            name: base,
            mtimeMs: st.mtimeMs,
            size: st.size,
          });
        }
      }
    }
  }

  walk(root);
  hits.sort((a, b) => a.module.localeCompare(b.module, undefined, { sensitivity: 'base' }));
  return hits;
}
