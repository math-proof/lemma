#!/usr/bin/env node
/**
 * scanLemmaPaths.mjs
 * ==================
 * Walk every `Lemma/**.lean` (generated `*.echo.lean` are skipped) and check whether the
 * file's *path* is consistent with the path its main lemma's statement suggests —
 * README "Lemma Naming Convention".
 *
 * Offline scan uses `mjs/lemmaPath.mjs` (lean.js AST, no Lean build):
 * the whole tree takes a couple of seconds.
 *
 *   node mjs/scanLemmaPaths.mjs                      # report the problem files only
 *   node mjs/scanLemmaPaths.mjs --all                # also list the consistent ones
 *   node mjs/scanLemmaPaths.mjs --filter Kernel/     # keep only paths containing a string
 *   node mjs/scanLemmaPaths.mjs --limit 200
 *   node mjs/scanLemmaPaths.mjs --json report.json
 *
 * Exit code: 0 when nothing needs fixing, 1 when some file is inconsistent / unreadable.
 */
import fs from 'fs';
import path from 'path';
import { REPO_ROOT } from '../server/lean/modulePath.mjs';
import { suggest } from './lemmaPath.mjs';

const LEMMA_ROOT = path.join(REPO_ROOT, 'Lemma');

function usage() {
  console.error(`usage: node mjs/scanLemmaPaths.mjs [options]

  --all             also list consistent lemmas (default: problems only)
  --filter <str>    only scan paths containing <str>   (e.g. Kernel/, Set/MinSetOf/)
  --limit <n>       stop after n files
  --json <file>     also write the full report as JSON
  -h, --help        this message`);
}

function parseArgs(argv) {
  const opts = {
    all: false,
    filter: null,
    limit: 0,
    json: null,
    help: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--all') opts.all = true;
    else if (a === '-h' || a === '--help') opts.help = true;
    else if (a === '--filter') opts.filter = argv[++i] ?? '';
    else if (a === '--limit') opts.limit = Number(argv[++i] || 0) || 0;
    else if (a === '--json') {
      const next = argv[++i];
      if (!next || next.startsWith('-')) throw new Error('--json needs a file path');
      opts.json = next;
    } else if (a === '--precise' || a === '--batch' || a === '--chunk-size') {
      throw new Error(
        `${a} removed: Lean Name.toJson scanning is gone; use default lean.js AST mode ` +
          `(or node mjs/lemmaPath.mjs --json <file>)`,
      );
    } else throw new Error(`unknown option: ${a}`);
  }
  return opts;
}

function listLemmaFiles(dir = LEMMA_ROOT, out = []) {
  for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
    if (e.name.startsWith('.')) continue;
    const p = path.join(dir, e.name);
    if (e.isDirectory()) listLemmaFiles(p, out);
    else if (e.name.endsWith('.lean') && !e.name.endsWith('.echo.lean')) out.push(p);
  }
  return out;
}

/** `E:\github\lean\Lemma\Set\Foo.lean` → `Lemma/Set/Foo.lean` */
function relLemma(abs) {
  return `Lemma/${path.relative(LEMMA_ROOT, abs).replace(/\\/g, '/')}`;
}

/** lean.js AST check (offline, ~0.4 ms/file). */
function checkOffline(abs) {
  const r = suggest(abs);
  const c = r.consistent || {};
  return {
    file: relLemma(abs),
    method: 'lean.js',
    current: `Lemma/${r.currentPath}`,
    want: `Lemma/${r.suggestedPath}`,
    ok: !!c.ok,
    reason: c.reason || '',
  };
}



function printResult(r, showOk) {
  if (r.error) {
    console.log(`unreadable    ${r.file}`);
    console.log(`              ${r.error}`);
  } else if (r.ok) {
    if (showOk) console.log(`ok            ${r.file}`);
  } else {
    console.log(`inconsistent  ${r.file}`);
    console.log(`              path: ${r.current}`);
    if (r.want) console.log(`              want: ${r.want}`);
    if (r.reason) console.log(`              why:  ${r.reason}`);
  }
}

/** Per-file checks: offline lean.js AST via lemmaPath.mjs. */
async function runSequential(files, results) {
  for (let i = 0; i < files.length; i++) {
    const abs = files[i];
    try {
      results.push(checkOffline(abs));
    } catch (e) {
      results.push({
        file: relLemma(abs),
        method: 'lean.js',
        ok: false,
        error: String(e?.message || e).split('\n')[0],
      });
    }
    if ((i + 1) % 200 === 0) process.stderr.write(`\r… ${i + 1}/${files.length}`);
  }
  if (files.length >= 200) process.stderr.write('\n');
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  if (opts.help) {
    usage();
    return;
  }

  let files = listLemmaFiles().sort();
  if (opts.filter) files = files.filter((f) => relLemma(f).includes(opts.filter));
  if (opts.limit) files = files.slice(0, opts.limit);
  if (!files.length) {
    console.error('no lemma matches');
    process.exitCode = 1;
    return;
  }
  const started = Date.now();
  const results = [];

  const counts = (rs) => ({
    consistent: rs.filter((r) => r.ok).length,
    inconsistent: rs.filter((r) => !r.ok && !r.error).length,
    unreadable: rs.filter((r) => r.error).length,
  });

  /**
   * Write the JSON report *before* any stdout use — a run whose stdout/stderr pipes
   * went away (detached launcher session) died mid-print and never reached the write
   * at the old bottom position. In `--batch` mode this also fires after every chunk,
   * so a crash never loses what has already been scanned.
   */
  const writeReport = (rs) => {
    if (!opts.json) return;
    fs.writeFileSync(
      path.resolve(opts.json),
      JSON.stringify(
        {
          method: 'lean.js',
          scanned: rs.length,
          counts: counts(rs),
          results: rs,
        },
        null,
        2,
      ),
    );
  };

  await runSequential(files, results);
  writeReport(results);

  const bad = results.filter((r) => !r.ok && !r.error);
  const unreadable = results.filter((r) => r.error);
  for (const r of opts.all ? results : results.filter((r) => !r.ok)) {
    printResult(r, opts.all && !r.ok);
  }

  const secs = ((Date.now() - started) / 1000).toFixed(1);
  console.log(
    `\nscanned ${results.length} lemma(s) with lean.js AST in ${secs}s — ` +
      `${results.length - bad.length - unreadable.length} consistent, ` +
      `${bad.length} inconsistent, ${unreadable.length} unreadable`,
  );
  console.log('inspect one file: node mjs/lemmaPath.mjs [--json] <file>');

  if (bad.length || unreadable.length) process.exitCode = 1;
}

main().catch((e) => {
  console.error(e.message || e);
  process.exit(1);
});
