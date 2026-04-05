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

/**
 * Directory matching PHP `index.php` `$path_info` for a dotted module:
 * `Tensor` → `Lemma/Tensor`, `Tensor.GetDot` → `Lemma/Tensor/GetDot`.
 * For `Foo#bar` → `Lemma/Foo/bar` (Lean submodule path segment).
 * Returns `null` if the resolved path would escape `Lemma/`.
 */
export function moduleToLemmaPackageDir(module, repoRoot = REPO_ROOT) {
  if (!module || typeof module !== 'string') return null;
  let m = module.trim().replace(/\//g, '.');
  if (m.endsWith('.lean')) {
    m = m.slice(0, -4);
  }
  const lemmaRoot = path.resolve(repoRoot, 'Lemma');
  let resolved;
  const hash = m.indexOf('#');
  if (hash !== -1) {
    const base = m.slice(0, hash);
    const rest = m.slice(hash + 1);
    if (!rest) return null;
    resolved = path.resolve(lemmaRoot, ...base.split('.').filter(Boolean), rest);
  } else {
    const parts = m.split('.').filter(Boolean);
    if (parts.length === 0) return null;
    resolved = path.resolve(lemmaRoot, ...parts);
  }
  const rel = path.relative(lemmaRoot, resolved);
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) return null;
  return resolved;
}

export function dirExists(absPath) {
  try {
    return fs.statSync(absPath).isDirectory();
  } catch {
    return false;
  }
}

/**
 * Same idea as `php/package.php`: subdirs → `packages`, `*.lean` (not `*.echo.lean`) → `theorems` (names without `.lean`).
 * Each entry is `{ name, mtimeMs, size }` (`size` is `null` for folders, like Explorer’s details view).
 */
export function listLemmaPackageContents(dirAbs) {
  /** @type {{ name: string; mtimeMs: number; size: number | null }[]} */
  const packages = [];
  /** @type {{ name: string; mtimeMs: number; size: number }[]} */
  const theorems = [];
  let entries;
  try {
    entries = fs.readdirSync(dirAbs, { withFileTypes: true });
  } catch {
    return { packages, theorems };
  }
  for (const ent of entries) {
    const name = ent.name;
    if (name === '.' || name === '..') continue;
    const full = path.join(dirAbs, name);
    let st;
    try {
      st = fs.statSync(full);
    } catch {
      continue;
    }
    if (st.isDirectory()) {
      packages.push({ name, mtimeMs: st.mtimeMs, size: null });
    } else if (name.endsWith('.lean') && !name.endsWith('.echo.lean')) {
      theorems.push({
        name: name.slice(0, -'.lean'.length),
        mtimeMs: st.mtimeMs,
        size: st.size,
      });
    }
  }
  const byName = (/** @type {{ name: string }} */ a, /** @type {{ name: string }} */ b) =>
    a.name.localeCompare(b.name, undefined, { sensitivity: 'base' });
  packages.sort(byName);
  theorems.sort(byName);
  return { packages, theorems };
}
