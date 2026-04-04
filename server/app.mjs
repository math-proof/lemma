/**
 * Lean lemma browser — pure Node.js (reads `.lean` files, JS compiler, EJS shell).
 * Optional MySQL cache: same idea as php/lemma.php (`.echo.lean` + `fetch_from_mysql`).
 */
import express from 'express';
import path from 'path';
import {
  REPO_ROOT,
  moduleToLeanPath,
  titleFromModule,
  readLeanFile,
  fileExists,
} from './lean/modulePath.mjs';
import { echo2vueFromSource, render2vueFromSource } from './lean/compiler/index.mjs';
import { jsonForScriptEmbed } from './lean/jsonForScriptEmbed.mjs';
import { listLemmaTopLevelDirs } from './lean/lemmaSections.mjs';
import { handleExecute } from './lean/execute.mjs';
import { handleDisambiguate } from './lean/disambiguate.mjs';
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

/** Same contract as `php/request/echo.php` (POST `module` → JSON `render` payload). */
app.post('/lean/php/request/echo.php', (req, res) => {
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
    const code = echo2vueFromSource(source, {
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

async function renderLemmaPage(res, module) {
  const abs = moduleToLeanPath(module);
  if (!abs || !fileExists(abs)) {
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

function handleLeanGet(req, res) {
  const module = req.query.module;
  if (!module || typeof module !== 'string') {
    res.status(400).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>lemma</title>
      <p>Add <code>?module=Section.Name.eq.Leaf</code>.</p>`
    );
    return;
  }
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
  res.type('html').send(`<!DOCTYPE html><meta charset="utf-8">
    <title>lemma</title>
    <p>Lean server (Node). Example:
    <a href="/lean/?module=Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax">/lean/?module=…</a></p>`);
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
