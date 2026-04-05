import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.join(__dirname, '..', '..');

/**
 * Map a `.lean` filesystem path to dotted module under `Lemma/`, matching PHP `lean_to_module`
 * (`php/utility.php`) and `index.php` (redirect when `module` ends with `.lean`).
 * Accepts absolute paths or paths relative to `Lemma/`.
 */
export function leanPathToModule(input, repoRoot = REPO_ROOT) {
  const trimmed = String(input).trim();
  if (!trimmed.endsWith('.lean')) {
    return null;
  }
  const lemmaRoot = path.join(repoRoot, 'Lemma');
  const resolved = path.isAbsolute(trimmed)
    ? path.normalize(trimmed)
    : path.normalize(
        path.join(lemmaRoot, trimmed.replace(/\//g, path.sep))
      );
  const rel = path.relative(path.resolve(lemmaRoot), path.resolve(resolved));
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) {
    return null;
  }
  const parts = rel.split(/[/\\]/).filter(Boolean);
  if (parts.length === 0) {
    return null;
  }
  const last = parts[parts.length - 1];
  if (!last.endsWith('.lean')) {
    return null;
  }
  parts[parts.length - 1] = last.slice(0, -'.lean'.length);
  return parts.join('.');
}

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
