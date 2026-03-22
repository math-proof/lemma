/**
 * Lean lemma browser — pure Node.js (reads `.lean` files, JS compiler, EJS shell).
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
import { render2vueFromSource } from './lean/compiler/index.mjs';
import { jsonForScriptEmbed } from './lean/jsonForScriptEmbed.mjs';
import { listLemmaTopLevelDirs } from './lean/lemmaSections.mjs';
import { handleExecutePhpStub } from './lean/executeStub.mjs';
import { handleDisambiguatePhp } from './lean/disambiguateStub.mjs';

const VIEWS = path.join(REPO_ROOT, 'views');

const app = express();
const PORT = Number(process.env.PORT || 3000);

app.set('view engine', 'ejs');
app.set('views', VIEWS);

app.use(express.urlencoded({ extended: true, limit: '50mb' }));

/** Matches PHP `php/request/sections.php` (POST → JSON array of `Lemma/` child dir names). */
app.post('/lean/php/request/sections.php', (_req, res) => {
  res.json(listLemmaTopLevelDirs());
});

/** Stub: no MySQL — returns empty SELECTs / fake rowcount so the UI does not 404. */
app.post('/lean/php/request/execute.php', handleExecutePhpStub);

/** Filesystem disambiguation (same idea as PHP `disambiguate.php`). */
app.post('/lean/php/request/disambiguate.php', handleDisambiguatePhp);

app.use(
  '/lean/static',
  express.static(path.join(REPO_ROOT, 'static'), {
    fallthrough: true,
    maxAge: process.env.NODE_ENV === 'production' ? '1h' : 0,
  })
);

function renderLemmaPage(res, module) {
  const abs = moduleToLeanPath(module);
  if (!abs || !fileExists(abs)) {
    res.status(404).type('html').send(
      `<!DOCTYPE html><meta charset="utf-8"><title>Not found</title>
      <p>No Lean file for module <code>${escapeHtml(module)}</code></p>
      <p>Expected: <code>${escapeHtml(abs || '')}</code></p>`
    );
    return;
  }
  const source = readLeanFile(abs);
  const code = render2vueFromSource(source, module, { user: 'lean' });
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
  renderLemmaPage(res, module);
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
  console.log(`Lemma server  http://127.0.0.1:${PORT}/lean/`);
  console.log(`  static:      /lean/static/`);
  console.log(`  compiler:    JS (render2vue.mjs)`);
});
