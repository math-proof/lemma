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

const VIEWS = path.join(REPO_ROOT, 'views');

const app = express();
const PORT = Number(process.env.PORT || 80);

app.set('view engine', 'ejs');
app.set('views', VIEWS);

app.use(express.urlencoded({ extended: true, limit: '50mb' }));

/** Matches PHP `php/request/sections.php` (POST → JSON array of `Lemma/` child dir names). */
app.post('/lean/php/request/sections.php', (_req, res) => {
  res.json(listLemmaTopLevelDirs());
});

/** Same contract as `php/request/execute.php` (`mysql\execute`); stub when `MYSQL_HOST` unset. */
app.post('/lean/php/request/execute.php', (req, res) => {
  handleExecute(req, res).catch((e) => {
    console.error('[execute]', e);
    res.status(500).type('text/plain').send('0');
  });
});

/** Filesystem disambiguation (same idea as PHP `disambiguate.php`). */
app.post('/lean/php/request/disambiguate.php', handleDisambiguate);

/** Recent modules (PHP `php/request/recent.php`); uses file mtimes. */
app.get('/lean/php/request/recent.php', handleRecent);

/** Same contract as `php/request/echo.php` (POST `module` → JSON `render` payload). */
app.post('/lean/php/request/echo.php', async (req, res) => {
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

app.use(
  '/lean/static',
  express.static(path.join(REPO_ROOT, 'static'), {
    fallthrough: true,
    maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
  })
);

const PROJECT_USER =
  process.env.LEAN_PROJECT_USER || path.basename(REPO_ROOT);

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
  res.render('package', { title, payloadJson });
}

async function renderLemmaPage(res, module) {
  const abs = moduleToLeanPath(module);
  const leanMissing = !abs || !fileExists(abs);
  if (leanMissing) {
    /** Same as PHP `index.php`: folder `Lemma/<module path>/` → `php/package.php` + `axiomContents`. */
    const pkgDir = moduleToLemmaPackageDir(module);
    if (pkgDir && dirExists(pkgDir)) {
      renderPackageBrowserPage(res, module);
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

async function handleLeanGet(req, res) {
  const raw = req.query.module;
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
    res.redirect(302, `/lean/?module=${encodeURIComponent(canonical)}`);
    return;
  }
  module = module.replace(/\//g, '.');
  renderLemmaPage(res, module).catch((err) => {
    console.error('[lean]', err);
    res.status(500).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Server error</title>
      <p>${escapeHtml(err.message)}</p>`
    );
  });
}

app.get('/lean', handleLeanGet);
app.get('/lean/', handleLeanGet);

app.get('/', (_req, res) => {
  res.redirect(302, '/lean/');
});

app.listen(PORT, '0.0.0.0', () => {
  const origin =
    PORT === 80 ? 'http://127.0.0.1' : `http://127.0.0.1:${PORT}`;
  console.log(`Lemma server  ${origin}/lean/`);
  console.log(`  static:      /lean/static/`);
  console.log(`  compiler:    JS (render2vue.mjs)`);
  if (getMysqlConfig()) {
    console.log('  mysql:       lemma from DB when row exists (.echo.lean gate like php/lemma.php)');
  }
});
