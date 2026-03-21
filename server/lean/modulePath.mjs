import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.join(__dirname, '..', '..');

/**
 * Map query module to filesystem path, mirroring the common case:
 * `Tensor.Foo.eq.Bar` → `Lemma/Tensor/Foo/eq/Bar.lean`
 * Supports `Foo#suffix` → `Foo/suffix.lean` (Lean submodule filename pattern used in PHP redirects).
 */
export function moduleToLeanPath(module) {
  if (!module || typeof module !== 'string') return null;
  let m = module.trim();
  if (m.endsWith('.lean')) {
    m = m.slice(0, -4).replace(/\//g, '.');
  }
  const hash = m.indexOf('#');
  if (hash !== -1) {
    const base = m.slice(0, hash);
    const rest = m.slice(hash + 1);
    const p = path.join(REPO_ROOT, 'Lemma', ...base.split('.'), `${rest}.lean`);
    return p;
  }
  const rel = path.join('Lemma', ...m.split('.')) + '.lean';
  return path.join(REPO_ROOT, rel);
}

export function titleFromModule(module) {
  return module.replace(/\./g, '/');
}

export function readLeanFile(absPath) {
  return fs.readFileSync(absPath, 'utf8');
}

export function fileExists(absPath) {
  try {
    fs.accessSync(absPath, fs.constants.R_OK);
    return true;
  } catch {
    return false;
  }
}
