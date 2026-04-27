/**
 * Lean lemma browser — pure Node.js (reads `.lean` files, JS compiler, EJS shell).
 * Optional MySQL cache: same idea as php/lemma.php (`.echo.lean` + `fetch_from_mysql`).
 */
import express from 'express';
import path from 'path';
import fs from 'fs/promises';
import {
  REPO_ROOT,
  moduleToLeanPath,
  moduleToLemmaPackageDir,
  leanPathToModule,
  titleFromModule,
  readLeanFile,
  fileExists,
  dirExists,
  listLemmaPackageContents,
} from './lean/modulePath.mjs';
import { echo2vueFromSource, render2vueFromSource } from './lean/compiler/index.mjs';
import { compile, LeanModule, LeanCaret } from '../static/js/parser/lean.js';
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

const VIEWS = path.join(REPO_ROOT, 'views');

const app = express();
const PORT = Number(process.env.PORT || 80);

const PROJECT_USER =
  process.env.LEAN_PROJECT_USER || path.basename(REPO_ROOT);

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

/** Lemma tree size for `website` home.md `<label id=count>` / `<label id=lines>`. */
app.get('/:userSegment/api/repo-stats.json', ensureProjectUser, async (_req, res) => {
  try {
    const { theoremCount, lineCount } = await getRepoStatsCached(PROJECT_USER);
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
  const userSeg = req.params.userSegment || PROJECT_USER;
  handleDeleteLemma(userSeg, req, res).catch((e) => {
    console.error('[delete-lemma]', e);
    res.status(500).json({ error: String(e?.message || e) });
  });
});

/** Same contract as `php/request/delete/package.php` (POST `package`, `section` → JSON `"deleted!"`). */
app.post('/:userSegment/php/request/delete/package.php', ensureProjectUser, (req, res) => {
  const userSeg = req.params.userSegment || PROJECT_USER;
  handleDeletePackage(userSeg, req, res).catch((e) => {
    console.error('[delete-package]', e);
    res.status(500).json({ error: String(e?.message || e) });
  });
});

/** Same contract as `php/request/rename.php` for POST `old` + `new` (dotted modules). */
app.post('/:userSegment/php/request/rename.php', ensureProjectUser, (req, res) => {
  const userSeg = req.params.userSegment || PROJECT_USER;
  handleRenameLemma(userSeg, req, res).catch((e) => {
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
    const { theoremCount } = await getRepoStatsCached(PROJECT_USER);
    res.type('text/plain; charset=utf-8').send(String(theoremCount));
  } catch (e) {
    console.error('[count.php]', e);
    res.status(500).type('text/plain').send('0');
  }
});

/** Plain text, same as `php/request/lines.php`. */
app.get('/:userSegment/php/request/lines.php', ensureProjectUser, async (_req, res) => {
  try {
    const { lineCount } = await getRepoStatsCached(PROJECT_USER);
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
    const abs = moduleToLeanPath(module);
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
    res.json(code);
  } catch (e) {
    console.error('[lean echo]', e);
    res.status(500).json({ error: String(e?.message || e) });
  }
});

/** Static files under `/:userSegment/static` (validates userSegment first). */
app.use('/:userSegment/static', ensureProjectUser, express.static(path.join(REPO_ROOT, 'static'), {
  fallthrough: true,
  maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
}));

async function renderSummaryPage(res, userSegment) {
  const { state_count_pairs, repertoire } = await buildSummaryPayload(PROJECT_USER);
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
    const pkgDir = moduleToLemmaPackageDir(pkgMod);
    if (pkgDir && dirExists(pkgDir)) {
      renderPackageBrowserPage(res, pkgMod, userSegment);
      return;
    }
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>No package folder for <code>${escapeHtml(pkgMod)}</code></p>`
    );
    return;
  }

  const abs = moduleToLeanPath(module);
  const leanMissing = !abs || !fileExists(abs);
  if (leanMissing) {
    /** Same as PHP `index.php`: folder `Lemma/<module path>/` → `php/package.php` + `axiomContents`. */
    const pkgDir = moduleToLemmaPackageDir(module);
    if (pkgDir && dirExists(pkgDir)) {
      renderPackageBrowserPage(res, module, userSegment);
      return;
    }
    const underscored = resolveUnderscoreModuleAlias(module);
    if (underscored) {
      const seg = userSegment || PROJECT_USER;
      res.redirect(302, `/${seg}/?module=${encodeURIComponent(underscored)}`);
      return;
    }
    const canonical = resolveMissingModuleRedirect(module);
    if (canonical) {
      const seg = userSegment || PROJECT_USER;
      res.redirect(302, `/${seg}/?module=${encodeURIComponent(canonical)}`);
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
      const row = await fetchLemmaRowFromMysql(PROJECT_USER, module);
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
  }

  const title = titleFromModule(module);
  const codeJson = jsonForScriptEmbed(code);
  res.set('Content-Type', 'text/html; charset=utf-8');
  res.render('lemma', { title, codeJson, userSegment });
}

function escapeHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
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

/** Same idea as `php/search.php` + `index.php` (`?type=`, `?q=`, `?latex=`). */
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
 * Lemma editor save (`render.vue` POST): write `Lemma/<module>.lean` and redirect to `?module=`.
 * PHP uses `php/lemma.php` inside `index.php`; Node assembles text in `assembleLemmaPost.mjs`.
 */
async function handleLemmaSavePost(res, userSegment, body) {
  let module = postFieldString(body.module).replace(/\//g, '.');
  if (!module || module.includes('..') || module.includes('\\')) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Bad request</title><p>Invalid module.</p>`
    );
    return;
  }
  const leanPath = moduleToLeanPath(module);
  if (!leanPath) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Bad request</title><p>Invalid module path.</p>`
    );
    return;
  }
  const lemmaRoot = path.join(REPO_ROOT, 'Lemma');
  const rel = path.relative(path.resolve(lemmaRoot), path.resolve(leanPath));
  if (!rel || rel.startsWith('..') || path.isAbsolute(rel)) {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Bad request</title><p>Module outside Lemma/.</p>`
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

  res.redirect(302, `/${userSegment}/?module=${encodeURIComponent(module)}`);
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
  const graph = await establishHierarchyGraph(PROJECT_USER, moduleStr, invert);
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
  const newTheoremJson = jsonForScriptEmbed(code);
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
    const userSegment = req.params.userSegment || PROJECT_USER;
    res.redirect(302, `/${userSegment}/?module=${encodeURIComponent(canonical)}`);
    return;
  }
  module = module.replace(/\//g, '.');
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

app.get('/', (_req, res) => {
  res.redirect(302, `/${PROJECT_USER}/`);
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
  getRepoStatsCached(PROJECT_USER).catch((e) =>
    console.warn('[repo-stats warm]', e?.message || e)
  );
});
