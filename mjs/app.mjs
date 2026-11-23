/**
 * Lean lemma browser — pure Node.js (reads `.lean` files, JS compiler, EJS shell).
 * Optional MySQL cache: same idea as php/lemma.php (`.echo.lean` + `fetch_from_mysql`).
 */
import express from 'express';
import path from 'path';
import fs from 'fs/promises';
import {
  REPO_ROOT,
  DECL_LIBRARY_FOLDERS,
  moduleToLeanPath,
  moduleToRepoLeanPath,
  leanFilePathToModule,
  moduleToLemmaPackageDir,
  leanPathToModule,
  titleFromModule,
  readLeanFile,
  fileExists,
  dirExists,
  listLemmaPackageContents,
  stripDeclFolderPrefix,
} from './lean/modulePath.mjs';
import { echo2vueFromSource, render2vueFromSource } from './lean/compiler/index.mjs';
import { compile, LeanModule, LeanCaret } from '../js/parser/lean.js';
import { jsonForScriptEmbed } from './lean/jsonForScriptEmbed.mjs';
import { listLemmaTopLevelDirs } from './lean/lemmaSections.mjs';
import { handleExecute } from './lean/execute.mjs';
import { handleDisambiguate } from './lean/disambiguate.mjs';
import { buildSummaryPayload } from './lean/summaryData.mjs';
import { handleRecent } from './lean/recent.mjs';
import {
  leanEchoPath,
  getMysqlConfig,
  shouldLoadLemmaFromMysql,
  fetchLemmaRowFromMysql,
  fetchMathlibLemmaPayloadsFromMysql,
  fetchMathlibRowByName,
  codeFromMysqlRow,
  ensureEmptyEchoFile,
} from './lean/fetchLemmaMysql.mjs';
import { buildNewTheoremCodeFromMathlibRow } from './lean/newTheoremBootstrap.mjs';
import { assembleLeanSourceFromPostBody } from './lean/assembleLemmaPost.mjs';
import { handleDeleteLemma } from './lean/deleteLemma.mjs';
import { handleDeletePackage } from './lean/deletePackage.mjs';
import { handleRenameLemma } from './lean/renameLemma.mjs';
import { buildSearchPayload, leanGetWantsSearch } from './lean/buildSearchPayload.mjs';
import {
  resolveMissingModuleRedirect,
  resolveUnderscoreModuleAlias,
} from './lean/moduleResolve.mjs';
import {
  establishHierarchyGraph,
  detectCycleTraceback,
  buildHierarchyTraceback,
} from './lean/hierarchyData.mjs';
import { renderWebsiteIndex, handleWebsiteMdPhp } from './lean/website.mjs';
import { handleMathlibPhpRequest } from './lean/mathlibRequest.mjs';
import { getRepoStatsCached } from './lean/lemmaRepoStats.mjs';
import {
  searchLeanFilesRecursiveUnderFolder,
  FOLDER_LEAN_SEARCH_MAX_HITS,
} from './lean/folderLeanSearch.mjs';

const VIEWS = path.join(REPO_ROOT, 'ejs');

const app = express();
const PORT = Number(process.env.PORT || 80);

const PROJECT_USER =
  process.env.LEAN_PROJECT_USER || path.basename(REPO_ROOT);

/**
 * `render2vue` / `echo2vue` still emit `error`; the `lemma` DB column and the
 * render/newTheorem Vue pages now use `meta.error` — same move as php/lemma.php.
 * render.vue reads `meta.error` in its template, so embedded payloads must carry `meta`.
 */
function normalizeCodeMeta(code) {
  let meta = code.meta;
  if (!meta || typeof meta !== 'object' || Array.isArray(meta)) meta = {};
  if (!Array.isArray(meta.error)) meta.error = Array.isArray(code.error) ? code.error : [];
  code.meta = meta;
  if ('error' in code) delete code.error;
  return code;
}

function ensureProjectUser(req, res, next) {
  if (req.params.userSegment !== PROJECT_USER) {
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>No site for user prefix <code>${escapeHtml(req.params.userSegment)}</code></p>`
    );
    return;
  }
  next();
}

app.set('view engine', 'ejs');
app.set('views', VIEWS);

app.use(express.urlencoded({ extended: true, limit: '50mb' }));

// Prevent browser caching of EJS-rendered HTML pages (static files override this via express.static)
app.use((req, res, next) => { res.set('Cache-Control', 'no-store'); next(); });

// katex is installed from npm (node_modules/katex). Serve that package only —
// not the rest of node_modules — and keep pages that still request the vendored
// unpkg path (`/unpkg.com/katex@0.16.21/…` and `…/static/unpkg.com/katex@0.16.21/…`).
const KATEX_PKG = path.join(REPO_ROOT, 'node_modules', 'katex');
const katexFiles = express.static(KATEX_PKG, {
  index: false,
  fallthrough: false,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
});
app.use('/node_modules/katex', katexFiles);
app.use('/lean/node_modules/katex', katexFiles);
app.use((req, res, next) => {
  const marker = '/unpkg.com/katex@0.16.21/';
  const at = req.path.indexOf(marker);
  if (at < 0) return next();
  const rel = req.path.slice(at + marker.length);
  if (!rel || rel.includes('..')) return res.status(400).end();
  const q = req.url.includes('?') ? req.url.slice(req.url.indexOf('?')) : '';
  req.url = '/' + rel + q;
  return katexFiles(req, res, next);
});

// axios is installed from npm (node_modules/axios). Same as katex: this package only,
// and leftover `/unpkg.com/axios@0.24.0/` requests (including under /static/) still resolve.
const AXIOS_PKG = path.join(REPO_ROOT, 'node_modules', 'axios');
const axiosFiles = express.static(AXIOS_PKG, {
  index: false,
  fallthrough: false,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
});
app.use('/node_modules/axios', axiosFiles);
app.use('/lean/node_modules/axios', axiosFiles);
app.use((req, res, next) => {
  const marker = '/unpkg.com/axios@0.24.0/';
  const at = req.path.indexOf(marker);
  if (at < 0) return next();
  const rel = req.path.slice(at + marker.length);
  if (!rel || rel.includes('..')) return res.status(400).end();
  const q = req.url.includes('?') ? req.url.slice(req.url.indexOf('?')) : '';
  req.url = '/' + rel + q;
  return axiosFiles(req, res, next);
});

// clipboard is installed from npm (node_modules/clipboard). This package only;
// leftover `/unpkg.com/clipboard@2.0.11/` requests still resolve.
const CLIPBOARD_PKG = path.join(REPO_ROOT, 'node_modules', 'clipboard');
const clipboardFiles = express.static(CLIPBOARD_PKG, {
  index: false,
  fallthrough: false,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
});
app.use('/node_modules/clipboard', clipboardFiles);
app.use('/lean/node_modules/clipboard', clipboardFiles);
app.use((req, res, next) => {
  const marker = '/unpkg.com/clipboard@2.0.11/';
  const at = req.path.indexOf(marker);
  if (at < 0) return next();
  const rel = req.path.slice(at + marker.length);
  if (!rel || rel.includes('..')) return res.status(400).end();
  const q = req.url.includes('?') ? req.url.slice(req.url.indexOf('?')) : '';
  req.url = '/' + rel + q;
  return clipboardFiles(req, res, next);
});

// file-saver is installed from npm (node_modules/file-saver). This package only;
// leftover `/unpkg.com/file-saver@2.0.5/` requests still resolve.
const FILE_SAVER_PKG = path.join(REPO_ROOT, 'node_modules', 'file-saver');
const fileSaverFiles = express.static(FILE_SAVER_PKG, {
  index: false,
  fallthrough: false,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
});
app.use('/node_modules/file-saver', fileSaverFiles);
app.use('/lean/node_modules/file-saver', fileSaverFiles);
app.use((req, res, next) => {
  const marker = '/unpkg.com/file-saver@2.0.5/';
  const at = req.path.indexOf(marker);
  if (at < 0) return next();
  const rel = req.path.slice(at + marker.length);
  if (!rel || rel.includes('..')) return res.status(400).end();
  const q = req.url.includes('?') ? req.url.slice(req.url.indexOf('?')) : '';
  req.url = '/' + rel + q;
  return fileSaverFiles(req, res, next);
});

// qs, vue, vue3-sfc-loader, lz-string, prismjs, highlight.js, marked: npm packages only.
// Relative page URLs are requested under /lean/node_modules/… as well as /node_modules/….
function mountNpmPkg(name, unpkgMarker) {
  const pkgDir = path.join(REPO_ROOT, 'node_modules', name);
  const files = express.static(pkgDir, {
    index: false,
    fallthrough: false,
    maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
  });
  app.use('/node_modules/' + name, files);
  app.use('/lean/node_modules/' + name, files);
  app.use((req, res, next) => {
    const at = req.path.indexOf(unpkgMarker);
    if (at < 0) return next();
    const rel = req.path.slice(at + unpkgMarker.length);
    if (!rel || rel.includes('..')) return res.status(400).end();
    const q = req.url.includes('?') ? req.url.slice(req.url.indexOf('?')) : '';
    req.url = '/' + rel + q;
    return files(req, res, next);
  });
}
mountNpmPkg('qs', '/unpkg.com/qs@6.10.2/');
mountNpmPkg('vue', '/unpkg.com/vue@3.5.13/');
mountNpmPkg('vue3-sfc-loader', '/unpkg.com/vue3-sfc-loader@0.9.5/');
mountNpmPkg('lz-string', '/unpkg.com/lz-string@1.5.0/');
mountNpmPkg('prismjs', '/unpkg.com/prismjs@1.30.0/');
mountNpmPkg('highlight.js', '/unpkg.com/highlight.js/8.8.0/');
mountNpmPkg('marked', '/unpkg.com/marked@2.1.3/');

// CodeMirror 6 packages are served from node_modules/@codemirror/*, @lezer/*, and style-mod
const CM6_SCOPES = ['@codemirror', '@lezer', '@marijn'];
for (const scope of CM6_SCOPES) {
  const pkgPath = path.join(REPO_ROOT, 'node_modules', scope);
  const files = express.static(pkgPath, {
    index: false,
    fallthrough: false,
    maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
  });
  app.use(`/node_modules/${scope}`, files);
  app.use(`/lean/node_modules/${scope}`, files);
}
// style-mod is a flat package (no scope)
for (const pkg of ['style-mod', 'crelt', 'w3c-keyname']) {
  const pkgPath = path.join(REPO_ROOT, 'node_modules', pkg);
  const files = express.static(pkgPath, {
    index: false,
    fallthrough: false,
    maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
  });
  app.use(`/node_modules/${pkg}`, files);
  app.use(`/lean/node_modules/${pkg}`, files);
}

app.get(['/py', '/py/'], (req, res) => res.redirect(302, `http://localhost:8080${req.originalUrl}`));

/** Serve real CM6 / Lezer package ESM from node_modules (import map → /__cm__/*). */
function resolveCmEsmEntrySync(pkg) {
  if (!pkg || pkg.includes('..') || pkg.startsWith('/') || pkg.includes('\\')) return null;
  // Scoped (@scope/name) or flat (name) only — matches ejs/codemirror-importmap.ejs
  if (!/^(@[\w.-]+\/[\w.-]+|[\w.-]+)$/.test(pkg)) return null;
  return path.join(REPO_ROOT, 'node_modules', pkg, 'package.json');
}

async function resolveCmEsmFile(pkg) {
  const pkgJsonPath = resolveCmEsmEntrySync(pkg);
  if (!pkgJsonPath) return null;
  let pkgJson;
  try {
    pkgJson = JSON.parse(await fs.readFile(pkgJsonPath, 'utf8'));
  } catch {
    return null;
  }
  let entry = pkgJson.exports;
  if (entry && typeof entry === 'object') {
    if (entry['.']) entry = entry['.'];
    if (typeof entry === 'object') entry = entry.import || entry.default || entry;
    if (typeof entry === 'object') entry = entry.default || entry.import;
  }
  if (typeof entry !== 'string') entry = pkgJson.module || pkgJson.main;
  if (typeof entry !== 'string') return null;
  const pkgDir = path.dirname(pkgJsonPath);
  const file = path.resolve(pkgDir, entry);
  if (!file.startsWith(pkgDir + path.sep)) return null;
  try {
    await fs.access(file);
  } catch {
    return null;
  }
  return file;
}

app.get('/:userSegment/__cm__/*pkg', async (req, res) => {
  try {
    const pkg = Array.isArray(req.params.pkg) ? req.params.pkg.join('/') : req.params.pkg;
    const file = await resolveCmEsmFile(pkg);
    if (!file) {
      res.status(404).type('text').send(`// unknown package: ${pkg}`);
      return;
    }
    const src = await fs.readFile(file, 'utf8');
    res.set('Content-Type', 'text/javascript; charset=utf-8');
    res.set(
      'Cache-Control',
      process.env.NODE_ENV === 'production' ? 'public, max-age=3600' : 'no-store',
    );
    res.send(src);
  } catch (e) {
    console.error('[__cm__]', e);
    res.status(500).type('text').send(`// error: ${e.message}`);
  }
});

/** Lemma tree size for `website` home.md `<label id=count>` / `<label id=lines>`. */
app.get('/:userSegment/api/repo-stats.json', ensureProjectUser, async (_req, res) => {
  try {
    const { theoremCount, lineCount } = await getRepoStatsCached();
    res.set('Cache-Control', 'public, max-age=300');
    res.json({ theoremCount, lineCount });
  } catch (e) {
    console.error('[repo-stats]', e);
    res.status(500).json({ error: String(e?.message || e) });
  }
});

/**
 * Explorer folder search: recursive `.lean` files under `Lemma/<folder>/`.
 * Query: `folder` = dotted module (optional, empty = all `Lemma/`), `q` = substring (name or full module).
 */
app.get('/:userSegment/api/folder-search.json', ensureProjectUser, (req, res) => {
  try {
    const folder = String(req.query.folder ?? '');
    const q = String(req.query.q ?? '');
    const hits = searchLeanFilesRecursiveUnderFolder(folder, q);
    if (process.env.NODE_ENV !== 'production') {
      res.set('Cache-Control', 'no-store');
    }
    res.json({ hits, truncated: hits.length >= FOLDER_LEAN_SEARCH_MAX_HITS });
  } catch (e) {
    console.error('[folder-search]', e);
    res.status(500).json({ error: String(e?.message || e) });
  }
});

/** Matches PHP `php/request/sections.php` (POST → JSON array of `Lemma/` child dir names). */
app.post('/:userSegment/php/request/sections.php', ensureProjectUser, (_req, res) => {
  res.json(listLemmaTopLevelDirs());
});

/** Same contract as `php/request/execute.php` (`mysql\execute`); stub when `MYSQL_HOST` unset. */
app.post('/:userSegment/php/request/execute.php', ensureProjectUser, (req, res) => {
  handleExecute(req, res).catch((e) => {
    console.error('[execute]', e);
    res.status(500).type('text/plain').send('0');
  });
});

/** Same contract as `php/request/mathlib.php` (POST `name` → JSON from Lean `Name.toJson`). */
app.post('/:userSegment/php/request/mathlib.php', ensureProjectUser, (req, res) => {
  handleMathlibPhpRequest(req, res).catch((e) => {
    console.error('[mathlib.php]', e);
    res.status(500).json({ error: String(e?.message || e) });
  });
});

/** Same contract as `php/request/delete/lemma.php` (POST `package`, `lemma` → JSON `"deleted!"`). */
app.post('/:userSegment/php/request/delete/lemma.php', ensureProjectUser, (req, res) => {
  handleDeleteLemma(req, res).catch((e) => {
    console.error('[delete-lemma]', e);
    res.status(500).json({ error: String(e?.message || e) });
  });
});

/** Same contract as `php/request/delete/package.php` (POST `package`, `section` → JSON `"deleted!"`). */
app.post('/:userSegment/php/request/delete/package.php', ensureProjectUser, (req, res) => {
  handleDeletePackage(req, res).catch((e) => {
    console.error('[delete-package]', e);
    res.status(500).json({ error: String(e?.message || e) });
  });
});

/** Same contract as `php/request/rename.php` for POST `old` + `new` (dotted modules). */
app.post('/:userSegment/php/request/rename.php', ensureProjectUser, (req, res) => {
  handleRenameLemma(req, res).catch((e) => {
    console.error('[rename]', e);
    res.status(500).json({ error: String(e?.message || e) });
  });
});

/** Filesystem disambiguation (same idea as PHP `disambiguate.php`). */
app.post('/:userSegment/php/request/disambiguate.php', ensureProjectUser, handleDisambiguate);

/** Recent modules (PHP `php/request/recent.php`); uses file mtimes. */
app.get('/:userSegment/php/request/recent.php', ensureProjectUser, handleRecent);

/** Plain text, same as `php/request/count.php` (`select_count`). */
app.get('/:userSegment/php/request/count.php', ensureProjectUser, async (_req, res) => {
  try {
    const { theoremCount } = await getRepoStatsCached();
    res.type('text/plain; charset=utf-8').send(String(theoremCount));
  } catch (e) {
    console.error('[count.php]', e);
    res.status(500).type('text/plain').send('0');
  }
});

/** Plain text, same as `php/request/lines.php`. */
app.get('/:userSegment/php/request/lines.php', ensureProjectUser, async (_req, res) => {
  try {
    const { lineCount } = await getRepoStatsCached();
    res.type('text/plain; charset=utf-8').send(String(lineCount));
  } catch (e) {
    console.error('[lines.php]', e);
    res.status(500).type('text/plain').send('0');
  }
});

/** Same contract as `php/request/segment_detection.php` (POST `lean` → JSON `{lean}`). */
app.post('/:userSegment/php/request/segment_detection.php', ensureProjectUser, (req, res) => {
  const lean = req.body?.lean;
  if (typeof lean !== 'string') {
    res.status(400).json({ error: 'missing lean' });
    return;
  }
  try {
    const code = compile(lean + '\n');
    if (!(code instanceof LeanModule)) {
      res.status(500).json({ error: 'compile() root must be LeanModule' });
      return;
    }
    // If first arg is LeanCaret, remove it (matches PHP logic)
    if (code.args[0] instanceof LeanCaret) {
      code.args.shift();
    }
    // Stringify and trim (PHP rtrim("$code"))
    const result = String(code).replace(/\s+$/, '');
    res.json({ lean: result });
  } catch (e) {
    console.error('[segment_detection]', e);
    res.json({ error: String(e?.message || e) });
  }
});

/** Same contract as `php/request/echo.php` (POST `module` → JSON `render` payload). */
app.post('/:userSegment/php/request/echo.php', ensureProjectUser, async (req, res) => {
  try {
    const {module} = req.body;
    if (!module || typeof module !== 'string') {
      res.status(400).json({ error: 'missing module' });
      return;
    }
    const abs = moduleToRepoLeanPath(module);
    if (!abs || !fileExists(abs)) {
      res.status(404).json({ error: 'not found', module });
      return;
    }
    const source = readLeanFile(abs);
    const code = await echo2vueFromSource(source, {
      module,
      leanAbsPath: abs,
    });
    code.user = PROJECT_USER;
    res.json(normalizeCodeMeta(code));
  } catch (e) {
    console.error('[lean echo]', e);
    res.status(500).json({ error: String(e?.message || e) });
  }
});

/** Top-level `ico/` (favicon etc.) served under `/:userSegment/ico`. */
app.use('/:userSegment/ico', ensureProjectUser, express.static(path.join(REPO_ROOT, 'ico'), {
  fallthrough: true,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
}));

// Top-level `vue/` (single-file components) and its `../js/…` imports from the
// SFCs resolve to `js/` via the parallel `/:userSegment/js` mount.
app.use('/:userSegment/vue', ensureProjectUser, express.static(path.join(REPO_ROOT, 'vue'), {
  fallthrough: true,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
}));
app.use('/:userSegment/js', ensureProjectUser, express.static(path.join(REPO_ROOT, 'js'), {
  fallthrough: true,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
}));

// Top-level `css/` (stylesheets moved out of `static/`).
app.use('/:userSegment/css', ensureProjectUser, express.static(path.join(REPO_ROOT, 'css'), {
  fallthrough: true,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
}));

async function renderSummaryPage(res, userSegment) {
  const { state_count_pairs, repertoire } = await buildSummaryPayload();
  const summaryJson = jsonForScriptEmbed({ state_count_pairs, repertoire });
  res.set('Content-Type', 'text/html; charset=utf-8');
  res.render('summary', { summaryJson, userSegment });
}

function renderPackageBrowserPage(res, module, userSegment) {
  const pkgDir = moduleToLemmaPackageDir(module);
  if (!pkgDir || !dirExists(pkgDir)) {
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>No Lean file or package folder for module <code>${escapeHtml(module)}</code></p>`
    );
    return;
  }
  const { packages, theorems } = listLemmaPackageContents(pkgDir);
  const title = titleFromModule(module);
  const payloadJson = jsonForScriptEmbed({ packages, theorems });
  res.set('Content-Type', 'text/html; charset=utf-8');
  /** Avoid stale embedded JSON during dev (old process served string-only `theorems[]`). */
  if (process.env.NODE_ENV !== 'production') {
    res.set('Cache-Control', 'no-store');
  }
  res.render('package', { title, payloadJson, userSegment });
}

async function renderLemmaPage(res, module, userSegment) {
  module = stripDeclFolderPrefix(module);
  /**
   * PHP `index.php`: `?module=Section...Name.` (trailing `.`) makes `$title` end with `/`,
   * so `$leanFile` is never set and `package.php` runs — browse the folder, not `Name.lean`.
   * Node `path.join` drops empty segments, so `Name.` wrongly mapped to `.../Name.lean`.
   */
  const modTrim = module.trim();
  if (modTrim.endsWith('.')) {
    const pkgMod = modTrim.replace(/\.+$/, '');
    if (!pkgMod) {
      res.status(404).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
        <p>Invalid <code>module</code> (only trailing dots).</p>`
      );
      return;
    }
    /** `moduleToLemmaPackageDir` is Lemma-relative: namespace `Nat` → `Lemma/Nat`. */
    const relPkgMod = stripDeclFolderPrefix(pkgMod);
    const pkgDir = moduleToLemmaPackageDir(relPkgMod);
    if (pkgDir && dirExists(pkgDir)) {
      renderPackageBrowserPage(res, relPkgMod, userSegment);
      return;
    }
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>No package folder for <code>${escapeHtml(pkgMod)}</code></p>`
    );
    return;
  }

  const abs = moduleToRepoLeanPath(module);
  const leanMissing = !abs || !fileExists(abs);
  if (leanMissing) {
    /** Same as PHP `index.php`: folder `Lemma/<module path>/` → `php/package.php` + `axiomContents`. */
    const relPkgMod = stripDeclFolderPrefix(module);
    const pkgDir = moduleToLemmaPackageDir(relPkgMod);
    if (pkgDir && dirExists(pkgDir)) {
      renderPackageBrowserPage(res, relPkgMod, userSegment);
      return;
    }
    const underscored = resolveUnderscoreModuleAlias(module);
    if (underscored) {
      redirectToModule(res, userSegment, underscored);
      return;
    }
    const canonical = resolveMissingModuleRedirect(module);
    if (canonical) {
      redirectToModule(res, userSegment, canonical);
      return;
    }
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>No Lean file for module <code>${escapeHtml(module)}</code></p>
      <p>Expected: <code>${escapeHtml(abs || '')}</code></p>`
    );
    return;
  }

  const echoAbs = leanEchoPath(abs);
  let code = null;

  if (shouldLoadLemmaFromMysql(abs, echoAbs)) {
    try {
      const row = await fetchLemmaRowFromMysql(module);
      if (row) {
        code = codeFromMysqlRow(row, module, PROJECT_USER);
        if (code && !fileExists(echoAbs)) ensureEmptyEchoFile(echoAbs);
      }
    } catch (e) {
      console.warn('[lean mysql]', e.message);
    }
  }

  if (!code) {
    const source = readLeanFile(abs);
    code = render2vueFromSource(source, { user: PROJECT_USER });
    code.module = stripDeclFolderPrefix(module);
  }

  renderLemmaCode(res, code, module, userSegment);
}

function renderLemmaCode(res, code, module, userSegment) {
  const title = titleFromModule(module);
  const codeJson = jsonForScriptEmbed(normalizeCodeMeta(code));
  res.set('Content-Type', 'text/html; charset=utf-8');
  res.render('lemma', { title, codeJson, userSegment });
}

/**
 * `?theorem=<abs path | repo path | dotted module>`: resolve any `.lean` file under the repo.
 * Dotted addresses are Lean namespaces (`Rat.DivMulS.eq.Div.of.Ne_0`): prefer `Lemma/`,
 * then `Theorem/`. An explicit folder prefix (`Theorem.…`, `Lemma.…`, `Def.…`) is used as written.
 * Symlinks are resolved and the real path must stay inside the repo.
 */
async function resolveTheoremPath(input) {
  const raw = String(input ?? '').trim();
  if (!raw) return null;
  const cleaned = raw.replace(/[\\/]+$/, '');
  if (!cleaned.endsWith('.lean')) {
    const absModule = moduleToRepoLeanPath(cleaned);
    if (absModule && fileExists(absModule)) return absModule;
    return null;
  }
  const candidate = path.isAbsolute(cleaned) ? cleaned : path.join(REPO_ROOT, cleaned);
  let abs;
  let root;
  try {
    [abs, root] = await Promise.all([fs.realpath(candidate), fs.realpath(REPO_ROOT)]);
  } catch {
    return null;
  }
  if (!abs.endsWith('.lean')) return null;
  const rel = path.relative(root, abs);
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) return null;
  return abs;
}

/** Canonical `?theorem=` address for a file: the Lean namespace (no folder prefix). */
function theoremCanonicalModule(abs) {
  return leanFilePathToModule(abs);
}

async function renderTheoremPage(res, abs, userSegment) {
  const module = leanFilePathToModule(abs);
  if (!module) {
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>Cannot derive a module name for <code>${escapeHtml(abs)}</code></p>`
    );
    return;
  }
  // Same cache logic as `?module=` (`renderLemmaPage`): serve the MySQL row while the
  // echo file is stale/missing, otherwise parse-only; the client's echo POST fills proof LaTeX.
  const echoAbs = leanEchoPath(abs);
  let code = null;
  if (shouldLoadLemmaFromMysql(abs, echoAbs)) {
    try {
      const row = await fetchLemmaRowFromMysql(module);
      if (row) {
        code = codeFromMysqlRow(row, module, PROJECT_USER);
        if (code && !fileExists(echoAbs)) ensureEmptyEchoFile(echoAbs);
      }
    } catch (e) {
      console.warn('[lean mysql]', e.message);
    }
  }
  if (!code) {
    code = render2vueFromSource(readLeanFile(abs), { user: PROJECT_USER });
    code.module = stripDeclFolderPrefix(module);
  }
  renderLemmaCode(res, code, module, userSegment);
}

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * Redirect to `?module=`; put `#suffix` in the URL fragment (not `%23` in the query value).
 * Matches PHP `header("location:?module=$module")` when `$module` contains `#`.
 */
function redirectToModule(res, userSegment, module) {
  const seg = userSegment || PROJECT_USER;
  const hashIdx = module.indexOf('#');
  const base = hashIdx === -1 ? module : module.slice(0, hashIdx);
  const frag = hashIdx === -1 ? '' : `#${module.slice(hashIdx + 1)}`;
  const canonical = canonicalDeclParam(base);
  const query = canonical
    ? `${canonical.param}=${encodeURIComponent(canonical.value)}`
    : `module=${encodeURIComponent(base)}`;
  res.redirect(302, `/${seg}/?${query}${frag}`);
}

/** `Lemma.X` → `{param:'lemma', value:'X'}`, `Theorem.X` → `{param:'theorem', value:'X'}`. */
function canonicalDeclParam(module) {
  const match = /^(Lemma|Theorem)\.(.+)$/.exec(module);
  if (!match) return null;
  return { param: match[1] === 'Lemma' ? 'lemma' : 'theorem', value: match[2] };
}

/** PHP `index.php` `is_top_level_folder`: an existing capitalised repo directory (`Lemma`, `Def`, …). */
function isTopLevelFolder(head) {
  return /^[A-Z][A-Za-z0-9]*$/.test(head) && dirExists(path.join(REPO_ROOT, head));
}

/** `?lemma=Nat.Mul…` stays `Nat.Mul…`. Legacy `Lemma.` / `Theorem.` folder prefixes are stripped. */
function lemmaParamToModule(input) {
  let module = String(input ?? '').trim().replace(/\//g, '.');
  const hash = module.indexOf('#');
  if (hash !== -1) module = module.slice(0, hash);
  if (!module) return null;
  module = stripDeclFolderPrefix(module);
  return module || null;
}

/** `Lemma` or `Theorem` if `abs` lives in that repo folder, else null. */
function declFolderOfAbs(abs) {
  if (!abs) return null;
  const rel = path.relative(path.resolve(REPO_ROOT), path.resolve(abs));
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) return null;
  const folder = rel.split(/[/\\]/)[0];
  return DECL_LIBRARY_FOLDERS.includes(folder) ? folder : null;
}

function declQueryParam(folder) {
  return folder === 'Theorem' ? 'theorem' : 'lemma';
}

/** PHP `lean.php/website` → marketing/docs shell (`website/index.php`). */
/** No trailing-slash redirect: some proxies strip `/` and would loop with `→ /:userSegment/website/`. */
app.get(['/:userSegment/website', '/:userSegment/website/'], ensureProjectUser, renderWebsiteIndex);
app.use('/:userSegment/website/md.php', ensureProjectUser, (req, res) => {
  if (req.method !== 'GET') {
    res.status(405).type('text/plain').send('Method not allowed');
    return;
  }
  handleWebsiteMdPhp(req, res).catch((e) => {
    console.error('[website md.php]', e);
    res.status(500).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Error</title><p>${escapeHtml(String(e?.message || e))}</p>`
    );
  });
});
app.use('/:userSegment/website', ensureProjectUser, 
  express.static(path.join(REPO_ROOT, 'website'), {
  index: false,
  redirect: false,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
}));

/** Same idea as `php/search.php` + `index.php` (`?type=`, `?q=`, `?lean=`). */
async function renderSearchPage(res, dict, userSegment) {
  try {
    const payload = await buildSearchPayload(dict, PROJECT_USER);
    const searchJson = jsonForScriptEmbed(payload);
    res.set('Content-Type', 'text/html; charset=utf-8');
    if (process.env.NODE_ENV !== 'production') {
      res.set('Cache-Control', 'no-store');
    }
    res.render('search', { searchJson, userSegment });
  } catch (err) {
    console.error('[search]', err);
    res.status(500).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
      <p>${escapeHtml(String(err?.message || err))}</p>`
    );
  }
}

function postFieldString(val) {
  if (val == null) return '';
  if (Array.isArray(val)) return String(val[val.length - 1] ?? '').trim();
  return String(val).trim();
}

/**
 * Lemma editor save (`render.vue` POST): write the existing file under `Lemma/` or `Theorem/`
 * (prefer Lemma, then Theorem), or create `Lemma/<module>.lean` when the file is new.
 * PHP uses `php/lemma.php` inside `index.php`; Node assembles text in `assembleLemmaPost.mjs`.
 */
async function handleLemmaSavePost(res, userSegment, body) {
  let module = stripDeclFolderPrefix(postFieldString(body.module).replace(/\//g, '.'));
  if (!module || module.includes('..') || module.includes('\\')) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Bad request</title><p>Invalid module.</p>`
    );
    return;
  }
  const leanPath = moduleToRepoLeanPath(module) || moduleToLeanPath(module);
  if (!leanPath) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Bad request</title><p>Invalid module path.</p>`
    );
    return;
  }
  if (!declFolderOfAbs(leanPath)) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Bad request</title><p>Module outside Lemma/ or Theorem/.</p>`
    );
    return;
  }

  let text;
  try {
    text = await assembleLeanSourceFromPostBody(body);
  } catch (err) {
    console.error('[lemma-save]', err);
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Save failed</title>
      <p>${escapeHtml(String(err?.message || err))}</p>`
    );
    return;
  }

  await fs.mkdir(path.dirname(leanPath), { recursive: true });
  await fs.writeFile(leanPath, text, 'utf8');

  const folder = declFolderOfAbs(leanPath) || 'Lemma';
  res.redirect(302, `/${userSegment || PROJECT_USER}/?${declQueryParam(folder)}=${encodeURIComponent(module)}`);
}

/** POST body from `searchForm.vue` (PHP `index.php`); same logic as `/:userSegment/` POST. */
async function handleLeanPostSearch(req, res) {
  const userSegment = req.params.userSegment || PROJECT_USER;
  const body = req.body && typeof req.body === 'object' ? req.body : {};
  const moduleRaw = postFieldString(body.module);
  if (leanGetWantsSearch(body, moduleRaw)) {
    await renderSearchPage(res, body, userSegment);
    return;
  }
  const hasLemmaPayload =
    body.lemma != null && typeof body.lemma === 'object' && Object.keys(body.lemma).length > 0;
  if (moduleRaw && hasLemmaPayload) {
    await handleLemmaSavePost(res, userSegment, body);
    return;
  }
  res.redirect(302, `/${userSegment}/`);
}

async function renderHierarchyPage(res, query, keyInput, userSegment) {
  const v = query[keyInput];
  const moduleStr = typeof v === 'string' ? v.replace(/\//g, '.').trim() : '';
  if (!moduleStr) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>hierarchy</title>
      <p>Missing <code>${escapeHtml(keyInput)}</code> module.</p>`
    );
    return;
  }
  let deep = false;
  if (query.deep !== undefined && query.deep !== null && String(query.deep) !== '') {
    const d = query.deep;
    if (typeof d === 'string') {
      try {
        deep = JSON.parse(d);
      } catch {
        deep = d === 'true' || d === '1';
      }
    } else {
      deep = Boolean(d);
    }
  }
  const invert = keyInput === 'callee';
  const graph = await establishHierarchyGraph(moduleStr, invert);
  const parent = [];
  detectCycleTraceback(graph, moduleStr, parent);
  const traceback = buildHierarchyTraceback(parent, moduleStr);
  const hierarchyJson = jsonForScriptEmbed({
    module: moduleStr,
    graph,
    traceback,
    keyInput,
    deep,
  });
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') {
    res.set('Cache-Control', 'no-store');
  }
  res.render('hierarchy', { hierarchyJson, userSegment });
}

/**
 * PHP `index.php` default branch + `php/mathlib.php`: `?mathlib=name` → `mathlib.vue` with rows from `mathlib` table.
 */
async function renderMathlibPage(res, name, userSegment, limit) {
  const lemma = await fetchMathlibLemmaPayloadsFromMysql(name, limit);
  const mathlibJson = jsonForScriptEmbed({ lemma });
  const title = name ? String(name) : 'mathlib';
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') {
    res.set('Cache-Control', 'no-store');
  }
  res.render('mathlib', { title, mathlibJson, userSegment });
}

/**
 * PHP `php/new.php` + `index.php?new=`: edit shell for an existing `Lemma/<module>.lean` via `newTheorem.vue`.
 */
async function renderNewTheoremPage(res, module, userSegment) {
  const abs = moduleToLeanPath(module);
  let code;
  if (abs && fileExists(abs)) {
    const source = readLeanFile(abs);
    try {
      code = render2vueFromSource(source, { user: PROJECT_USER });
    } catch (err) {
      console.error('[new theorem]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
      return;
    }
  } else {
    const row = await fetchMathlibRowByName(module);
    if (!row) {
      res.status(404).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
        <p>No Lean file for <code>${escapeHtml(module)}</code> and no matching <code>mathlib</code> row (exact <code>name</code>).</p>
        <p>Configure MySQL (<code>MYSQL_HOST</code>, …) and ensure a row exists, or add <code>Lemma/…</code>. The PHP <code>axiom</code> bootstrap path is not implemented on Node.</p>`
      );
      return;
    }
    try {
      code = buildNewTheoremCodeFromMathlibRow(row, module);
      code.user = PROJECT_USER;
    } catch (err) {
      console.error('[new theorem mathlib]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
      return;
    }
  }
  if (!code.date || typeof code.date !== 'object') code.date = {};
  code.date.created = new Date().toISOString().slice(0, 10);
  delete code.date.updated;
  code.name = module;
  const newTheoremJson = jsonForScriptEmbed(normalizeCodeMeta(code));
  res.set('Content-Type', 'text/html; charset=utf-8');
  if (process.env.NODE_ENV !== 'production') {
    res.set('Cache-Control', 'no-store');
  }
  res.render('newTheorem', {
    title: module,
    newTheoremJson,
    userSegment,
  });
}

async function handleLeanGet(req, res) {
  const userSeg = req.params.userSegment || PROJECT_USER;

  /** `?theorem=<path | module>` — render any repo `.lean` file, not only `Lemma/`. */
  if (req.query.theorem != null && String(req.query.theorem).trim() !== '') {
    try {
      const raw = String(req.query.theorem).trim();
      const abs = await resolveTheoremPath(raw);
      if (!abs) {
        res.status(404).type('html').send(
          `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
          <p>Not a readable <code>.lean</code> file inside the repository:
          <code>${escapeHtml(raw)}</code></p>`
        );
        return;
      }
      // Canonicalise to the Lean namespace and the folder the file actually lives in
      // (`…/Theorem/Rat/…/Ne_0.lean` → `?theorem=Rat.…Ne_0`; a Lemma file → `?lemma=`).
      const canonical = theoremCanonicalModule(abs);
      const folder = declFolderOfAbs(abs);
      if (canonical) {
        const param = declQueryParam(folder || 'Theorem');
        const rawMod = raw.replace(/[\\/]+$/, '').endsWith('.lean')
          ? ''
          : stripDeclFolderPrefix(String(raw).trim().replace(/\//g, '.'));
        if (rawMod !== canonical || param !== 'theorem') {
          res.redirect(302, `/${userSeg}/?${param}=${encodeURIComponent(canonical)}`);
          return;
        }
      }
      await renderTheoremPage(res, abs, userSeg);
    } catch (err) {
      console.error('[theorem]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }

  /** `?lemma=<namespace>` — where `?module=Lemma.…` redirects to. */
  if (req.query.lemma != null && String(req.query.lemma).trim() !== '') {
    try {
      const raw = String(req.query.lemma).trim();
      if (raw.endsWith('.lean')) {
        const abs = await resolveTheoremPath(raw);
        const module = abs && leanFilePathToModule(abs);
        const folder = abs && declFolderOfAbs(abs);
        if (!module || !folder || !fileExists(abs) || !(await fs.stat(abs)).isFile()) {
          res.status(404).type('html').send(
            `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
            <p>Not a readable <code>.lean</code> file under <code>Lemma/</code> or <code>Theorem/</code>:
            <code>${escapeHtml(raw)}</code></p>`
          );
          return;
        }
        res.redirect(302, `/${userSeg}/?${declQueryParam(folder)}=${encodeURIComponent(module)}`);
        return;
      }
      const module = lemmaParamToModule(raw);
      if (!module) {
        res.status(404).type('html').send(
          `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
          <p>Not a module: <code>${escapeHtml(String(req.query.lemma))}</code></p>`
        );
        return;
      }
      const abs = moduleToRepoLeanPath(module);
      const folder = abs && declFolderOfAbs(abs);
      const param = folder === 'Theorem' ? 'theorem' : 'lemma';
      const rawMod = String(raw).trim().replace(/\//g, '.');
      if (param === 'theorem' || rawMod !== module) {
        res.redirect(302, `/${userSeg}/?${param}=${encodeURIComponent(module)}`);
        return;
      }
      await renderLemmaPage(res, module, userSeg);
    } catch (err) {
      console.error('[lemma]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }

  const raw = req.query.module;
  if (leanGetWantsSearch(req.query, raw)) {
    await renderSearchPage(res, req.query, userSeg);
    return;
  }

  const newRaw = req.query.new;
  if (newRaw != null && String(newRaw).trim() !== '') {
    const modNew = String(newRaw).trim().replace(/\//g, '.');
    try {
      await renderNewTheoremPage(res, modNew, userSeg);
    } catch (err) {
      console.error('[new]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }

  const calleeRaw = req.query.callee;
  if (calleeRaw != null && String(calleeRaw).trim() !== '') {
    try {
      await renderHierarchyPage(res, req.query, 'callee', userSeg);
    } catch (err) {
      console.error('[hierarchy callee]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }
  const callerRaw = req.query.caller;
  if (callerRaw != null && String(callerRaw).trim() !== '') {
    try {
      await renderHierarchyPage(res, req.query, 'caller', userSeg);
    } catch (err) {
      console.error('[hierarchy caller]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }

  /** PHP `index.php` + `php/mathlib.php`: `?mathlib=div_zero` (key may be present with empty value). */
  if (Object.prototype.hasOwnProperty.call(req.query, 'mathlib')) {
    const name = req.query.mathlib == null ? '' : String(req.query.mathlib).trim();
    const limRaw = req.query.limit;
    const limit =
      limRaw != null && String(limRaw).trim() !== '' ? Number(limRaw) : 100;
    try {
      await renderMathlibPage(res, name, userSeg, limit);
    } catch (err) {
      console.error('[mathlib]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }

  if (raw === undefined || raw === null || raw === '') {
    try {
      await renderSummaryPage(res, userSeg);
    } catch (err) {
      console.error('[summary]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }
  if (typeof raw !== 'string') {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>lemma</title>
      <p><code>module</code> must be a string (or omit it for the summary page).</p>`
    );
    return;
  }
  let module = raw.trim();
  if (!module) {
    try {
      await renderSummaryPage(res, userSeg);
    } catch (err) {
      console.error('[summary]', err);
      res.status(500).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
        <p>${escapeHtml(String(err?.message || err))}</p>`
      );
    }
    return;
  }
  /** Same as `index.php`: absolute or Lemma-relative `.lean` path → dotted module + redirect. */
  if (module.endsWith('.lean')) {
    const canonical = leanPathToModule(module);
    if (!canonical) {
      res.status(400).type('html').send(
        `<!DOCTYPE html><meta charset="utf-8"><title>lemma</title>
      <p>Could not resolve this <code>.lean</code> path to a module under <code>Lemma/</code>
      (must lie under this repo’s <code>Lemma</code> tree).</p>`
      );
      return;
    }
    redirectToModule(res, req.params.userSegment || PROJECT_USER, canonical);
    return;
  }
  module = module.replace(/\//g, '.');
  const hashInQuery = module.indexOf('#');
  if (hashInQuery !== -1) {
    module = module.slice(0, hashInQuery);
  }
  /** `?module=Lemma.…` → `?lemma=…`, `?module=Theorem.…` → `?theorem=…`. */
  const canonical = canonicalDeclParam(module);
  if (canonical) {
    res.redirect(302, `/${userSeg}/?${canonical.param}=${encodeURIComponent(canonical.value)}`);
    return;
  }
  /**
   * Legacy `?module=<Lemma-relative module>`: without a top-level prefix the module
   * resolves under `Lemma/`, so it is a lemma address — canonicalise it to `?lemma=`
   * (same as `index.php`), e.g. `?module=Matrix.Grad_Softmax.…` → `?lemma=Matrix.Grad_Softmax.…`.
   */
  if (!isTopLevelFolder(module.split('.')[0])) {
    res.redirect(302, `/${userSeg}/?lemma=${encodeURIComponent(module)}`);
    return;
  }
  renderLemmaPage(res, module, userSeg).catch((err) => {
    console.error('[lean]', err);
    res.status(500).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
      <p>${escapeHtml(err.message)}</p>`
    );
  });
}

app.get('/:userSegment', ensureProjectUser, handleLeanGet);
app.get('/:userSegment/', ensureProjectUser, handleLeanGet);
app.get('/:userSegment/index.php', ensureProjectUser, handleLeanGet);

/** Search form POST (PHP `index.php` + `search.php` use POST when form submits). */
function handleLeanPostSearchRoute(req, res) {
  handleLeanPostSearch(req, res).catch((err) => {
    console.error('[lean post]', err);
    res.status(500).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
      <p>${escapeHtml(String(err?.message || err))}</p>`
    );
  });
}

app.post('/:userSegment', ensureProjectUser, handleLeanPostSearchRoute);
app.post('/:userSegment/', ensureProjectUser, handleLeanPostSearchRoute);
app.post('/:userSegment/index.php', ensureProjectUser, handleLeanPostSearchRoute);

app.get('/', (req, res) => {
  const q = req.url.includes('?') ? req.url.slice(req.url.indexOf('?')) : '';
  res.redirect(302, `/${PROJECT_USER}/${q}`);
});

app.listen(PORT, '0.0.0.0', () => {
  const origin =
    PORT === 80 ? 'http://127.0.0.1' : `http://127.0.0.1:${PORT}`;
  console.log(`Lemma server  ${origin}/${PROJECT_USER}/`);
  console.log(`  static:      /${PROJECT_USER}/static/`);
  console.log(`  compiler:    JS (render2vue.mjs)`);
  if (getMysqlConfig()) {
    console.log('  mysql:       lemma from DB when row exists (.echo.lean gate like php/lemma.php)');
  }
  getRepoStatsCached().catch((e) =>
    console.warn('[repo-stats warm]', e?.message || e)
  );
});
