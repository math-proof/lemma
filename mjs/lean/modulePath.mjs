import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
export const REPO_ROOT = path.join(__dirname, '..', '..');

export function leanPathToModule(input, repoRoot = REPO_ROOT) {
  const trimmed = String(input).trim();
  if (!trimmed.endsWith(".lean")) {
    return null;
  }
  // PHP lean_to_module: walk parents until basename is Lemma, then join the collected segments.
  // Do not require the path to live under this machine's REPO_ROOT — VS Code / remote copy-paste
  // often hands `/home/.../Lemma/...` to `?module=`.
  const segs = trimmed.replace(/\\/g, "/").split("/").filter(Boolean);
  let lemmaAt = -1;
  for (let i = segs.length - 2; i >= 0; i--) {
    if (segs[i] === "Lemma") {
      lemmaAt = i;
      break;
    }
  }
  if (lemmaAt >= 0) {
    const parts = segs.slice(lemmaAt + 1);
    if (parts.length === 0 || parts.some((p) => p === ".." || p === ".")) return null;
    const last = parts[parts.length - 1];
    if (!last.endsWith(".lean")) return null;
    parts[parts.length - 1] = last.slice(0, -".lean".length);
    return parts.join(".");
  }
  // No Lemma segment: treat as relative to this repo's Lemma/ (existing Node behavior).
  const lemmaRoot = path.join(repoRoot, "Lemma");
  const resolved = path.isAbsolute(trimmed)
    ? path.normalize(trimmed)
    : path.normalize(
        path.join(
          lemmaRoot,
          trimmed.replace(/\//g, path.sep).replace(/^Lemma[/\\]/, "")
        )
      );
  const rel = path.relative(path.resolve(lemmaRoot), path.resolve(resolved));
  if (!rel || rel.startsWith("..") || path.isAbsolute(rel)) {
    return null;
  }
  const parts = rel.split(/[/\\]/).filter(Boolean);
  if (parts.length === 0) {
    return null;
  }
  const last = parts[parts.length - 1];
  if (!last.endsWith(".lean")) {
    return null;
  }
  parts[parts.length - 1] = last.slice(0, -".lean".length);
  return parts.join(".");
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

/** Repo folders that are not Lean namespaces and must not appear on page/DB module keys. */
export const DECL_LIBRARY_FOLDERS = ['Lemma', 'Theorem'];

/**
 * `Lemma.Random.X` / `Theorem.Random.X` → `Random.X`. Any other module is unchanged.
 */
export function stripDeclFolderPrefix(module) {
  const m = String(module ?? '').trim();
  const dot = m.indexOf('.');
  if (dot <= 0) return m;
  const head = m.slice(0, dot);
  if (DECL_LIBRARY_FOLDERS.includes(head)) return m.slice(dot + 1);
  return m;
}

/**
 * Dotted Lean namespace of any `.lean` file under the repo.
 * `/repo/Theorem/Rat/DivMulS/eq/Div/of/Ne_0.lean` → `Rat.DivMulS.eq.Div.of.Ne_0`
 * (the `Lemma/` / `Theorem/` folder is not part of the module name).
 * Other top-level folders are kept (`Def.Foo` stays `Def.Foo`).
 * Returns `null` for paths outside the repo or not ending in `.lean`.
 */
export function leanFilePathToModule(absPath, repoRoot = REPO_ROOT) {
  const abs = path.resolve(String(absPath));
  const rel = path.relative(path.resolve(repoRoot), abs);
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) return null;
  const parts = rel.split(/[/\\]/).filter(Boolean);
  const last = parts[parts.length - 1];
  if (!last || !last.endsWith('.lean')) return null;
  parts[parts.length - 1] = last.slice(0, -'.lean'.length);
  if (parts.length >= 2 && DECL_LIBRARY_FOLDERS.includes(parts[0])) parts.shift();
  if (parts.length === 0) return null;
  return parts.join('.');
}

/**
 * Resolve a Lean namespace or a legacy/explicit folder-prefixed module to a `.lean` file.
 * Bare names (`Random.X`, `Vector.X.eq.Y`) prefer `Lemma/`, then fall back to `Theorem/`.
 * An explicit first segment that is a repo folder (`Lemma.…`, `Theorem.…`, `Def.…`) is tried as written first.
 */
export function moduleToRepoLeanPath(module) {
  if (!module || typeof module !== 'string') return null;
  let m = module.trim();
  if (!m) return null;
  if (m.endsWith('.lean')) m = m.slice(0, -4).replace(/\//g, '.');
  if (m.includes('#')) {
    const lemma = moduleToLeanPath(m);
    return lemma && fileExists(lemma) ? lemma : null;
  }
  const parts = m.split('.').filter(Boolean);
  if (parts.length === 0 || parts.some((p) => p === '..' || p === '.')) return null;

  const tryAbs = (...segs) => {
    const abs = path.join(REPO_ROOT, ...segs) + '.lean';
    const rel = path.relative(path.resolve(REPO_ROOT), abs);
    if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) return null;
    return fileExists(abs) ? abs : null;
  };

  if (parts.length >= 2 && dirExists(path.join(REPO_ROOT, parts[0]))) {
    const abs = tryAbs(...parts);
    if (abs) return abs;
  }
  for (const folder of DECL_LIBRARY_FOLDERS) {
    const abs = tryAbs(folder, ...parts);
    if (abs) return abs;
  }
  return null;
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
