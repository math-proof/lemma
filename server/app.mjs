/**
 * Lean lemma browser — pure Node.js (reads `.lean` files, JS compiler, EJS shell).
 * Optional MySQL cache: same idea as php/lemma.php (`.echo.lean` + `fetch_from_mysql`).
 */
import express from 'express';
import path from 'path';
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
  codeFromMysqlRow,
  ensureEmptyEchoFile,
} from './lean/fetchLemmaMysql.mjs';
import { buildSearchPayload, leanGetWantsSearch } from './lean/buildSearchPayload.mjs';
import { resolveMissingModuleRedirect } from './lean/indexPhpModuleResolve.mjs';
import { renderWebsiteIndex, handleWebsiteMdPhp } from './lean/website.mjs';
import { getRepoStatsCached } from './lean/lemmaRepoStats.mjs';

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

async function renderSummaryPage(res) {
  const { state_count_pairs, repertoire } = await buildSummaryPayload(PROJECT_USER);
  const summaryJson = jsonForScriptEmbed({ state_count_pairs, repertoire });
  res.set('Content-Type', 'text/html; charset=utf-8');
  res.render('summary', { summaryJson });
}

function renderPackageBrowserPage(res, module) {
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
  res.render('package', { title, payloadJson });
}

async function renderLemmaPage(res, module, userSegment) {
  const abs = moduleToLeanPath(module);
  const leanMissing = !abs || !fileExists(abs);
  if (leanMissing) {
    /** Same as PHP `index.php`: folder `Lemma/<module path>/` → `php/package.php` + `axiomContents`. */
    const pkgDir = moduleToLemmaPackageDir(module);
    if (pkgDir && dirExists(pkgDir)) {
      renderPackageBrowserPage(res, module);
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
    code = render2vueFromSource(source, module, { user: PROJECT_USER });
  }

  const title = titleFromModule(module);
  const codeJson = jsonForScriptEmbed(code);
  res.set('Content-Type', 'text/html; charset=utf-8');
  res.render('lemma', { title, codeJson });
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
async function renderSearchPage(res, dict) {
  try {
    const payload = await buildSearchPayload(dict, PROJECT_USER);
    const searchJson = jsonForScriptEmbed(payload);
    res.set('Content-Type', 'text/html; charset=utf-8');
    if (process.env.NODE_ENV !== 'production') {
      res.set('Cache-Control', 'no-store');
    }
    res.render('search', { searchJson });
  } catch (err) {
    console.error('[search]', err);
    res.status(500).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
      <p>${escapeHtml(String(err?.message || err))}</p>`
    );
  }
}

/** POST body from `searchForm.vue` (PHP `index.php`); same logic as `/:userSegment/` POST. */
async function handleLeanPostSearch(req, res) {
  const body = req.body && typeof req.body === 'object' ? req.body : {};
  if (leanGetWantsSearch(body, body.module)) {
    await renderSearchPage(res, body);
    return;
  }
  const userSegment = req.params.userSegment || PROJECT_USER;
  res.redirect(302, `/${userSegment}/`);
}

async function handleLeanGet(req, res) {
  const raw = req.query.module;
  if (leanGetWantsSearch(req.query, raw)) {
    await renderSearchPage(res, req.query);
    return;
  }
  if (raw === undefined || raw === null || raw === '') {
    try {
      await renderSummaryPage(res);
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
      await renderSummaryPage(res);
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
  const userSeg = req.params.userSegment || PROJECT_USER;
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
