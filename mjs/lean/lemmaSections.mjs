import fs from 'fs';
import path from 'path';
import { REPO_ROOT } from './modulePath.mjs';

/**
 * Same idea as `request/sections`: top-level folder names under `Lemma/`
 * (used by `render.vue` → `regexp_section`).
 */
export function listLemmaTopLevelDirs() {
  const lemmaDir = path.join(REPO_ROOT, 'Lemma');
  if (!fs.existsSync(lemmaDir)) return [];
  return fs
    .readdirSync(lemmaDir, { withFileTypes: true })
    .filter((e) => e.isDirectory())
    .map((e) => e.name);
}
