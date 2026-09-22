#!/usr/bin/env node
/**
 * scanLemmaPaths.mjs
 * ==================
 * Walk every `Lemma/**.lean` (generated `*.echo.lean` are skipped) and check whether the
 * file's *path* is consistent with the path its main lemma's statement suggests —
 * README "Lemma Naming Convention".
 *
 * Offline scan (default) uses `mjs/suggestLemmaPath.mjs` (lean.js AST, no Lean build):
 * the whole tree takes a couple of seconds.
 *
 *   node mjs/scanLemmaPaths.mjs                      # report the problem files only
 *   node mjs/scanLemmaPaths.mjs --all                # also list the consistent ones
 *   node mjs/scanLemmaPaths.mjs --filter Kernel/     # keep only paths containing a string
 *   node mjs/scanLemmaPaths.mjs --limit 200
 *   node mjs/scanLemmaPaths.mjs --json report.json
 *
 * `--batch` checks the same Lean-elaborated type (`Name.toJson`) but with **one Lean
 * process per chunk of modules** instead of one per file — ≈4 min for the whole tree
 * (see `fetchLemmaJsonBatch`). Modules without an up-to-date `.olean` are reported instead
 * of checked.
 *
 *   node mjs/scanLemmaPaths.mjs --batch                  # whole tree, authoritative
 *   node mjs/scanLemmaPaths.mjs --batch --filter Kernel/
 *
 * `--precise` is the one-process-per-file variant (≈9 s per file) — same verdict, handy for
 * a single file:
 *
 *   node mjs/scanLemmaPaths.mjs --precise --filter Set/MinSetOf/
 *
 * Exit code: 0 when nothing needs fixing, 1 when some file is inconsistent / unreadable.
 */
import fs from 'fs';
import path from 'path';
import { REPO_ROOT } from '../server/lean/modulePath.mjs';
import { suggest } from './suggestLemmaPath.mjs';
import { suggestFromJson } from './suggestFromLean.mjs';
import { fetchLemmaJsonBatch } from './fetchLemmaJson.mjs';

const LEMMA_ROOT = path.join(REPO_ROOT, 'Lemma');

function usage() {
  console.error(`usage: node mjs/scanLemmaPaths.mjs [options]

  --all             also list consistent lemmas (default: problems only)
  --filter <str>    only scan paths containing <str>   (e.g. Kernel/, Set/MinSetOf/)
  --limit <n>       stop after n files
  --batch           check the Lean-elaborated type, one Lean process per chunk (≈4 min/tree)
  --chunk-size <n>  modules per Lean process in --batch (default 200)
  --precise         check the Lean-elaborated type, one Lean process per file (≈9 s/file)
  --json <file>     also write the full report as JSON (updated after every chunk)
  -h, --help        this message`);
}

function parseArgs(argv) {
  const opts = {
    all: false,
    filter: null,
    limit: 0,
    precise: false,
    batch: false,
    chunkSize: 200,
    json: null,
    help: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--all') opts.all = true;
    else if (a === '--precise') opts.precise = true;
    else if (a === '--batch') opts.batch = true;
    else if (a === '-h' || a === '--help') opts.help = true;
    else if (a === '--filter') opts.filter = argv[++i] ?? '';
    else if (a === '--limit') opts.limit = Number(argv[++i] || 0) || 0;
    else if (a === '--chunk-size') opts.chunkSize = Number(argv[++i] || 0) || 200;
    else if (a === '--json') {
      const next = argv[++i];
      if (!next || next.startsWith('-')) throw new Error('--json needs a file path');
      opts.json = next;
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

/** Lean `Name.toJson` check (needs the module built, ~1 lake env lean per file). */
async function checkPrecise(abs) {
  const { suggestFromLean } = await import('./suggestFromLean.mjs');
  const r = suggestFromLean(abs);
  return {
    file: relLemma(abs),
    method: 'lean',
    current: `Lemma/${r.currentPath}`,
    want: r.consistent
      ? `Lemma/${r.matchedSuggestion}`
      : r.suggestions[0]
        ? `Lemma/${r.suggestions[0]}`
        : '',
    ok: !!r.consistent,
    reason: r.consistent ? 'exact path match' : 'no alternative matches this path',
  };
}

/** Lean `Name.toJson` over `json` (from a batched probe) — same verdict, no Lean per file. */
function checkFromJson(file, json) {
  const r = suggestFromJson(json, file);
  return {
    file,
    method: 'lean-batch',
    current: `Lemma/${r.currentPath}`,
    want: r.consistent
      ? `Lemma/${r.matchedSuggestion}`
      : r.suggestions[0]
        ? `Lemma/${r.suggestions[0]}`
        : '',
    ok: !!r.consistent,
    reason: r.consistent ? 'exact path match' : 'no alternative matches this path',
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

/** Per-file checks: offline lean.js AST, or one `lake env lean` per file for `--precise`. */
async function runSequential(files, opts, results) {
  for (let i = 0; i < files.length; i++) {
    const abs = files[i];
    try {
      results.push(opts.precise ? await checkPrecise(abs) : checkOffline(abs));
    } catch (e) {
      results.push({
        file: relLemma(abs),
        method: opts.precise ? 'lean' : 'lean.js',
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
  if (opts.precise) {
    console.error(
      `precise: ${files.length} × lake env lean — this is slow, use --batch or --filter/--limit`,
    );
  }

  const started = Date.now();
  const results = [];

  const counts = (rs) => ({
    consistent: rs.filter((r) => r.ok).length,
    inconsistent: rs.filter((r) => !r.ok && !r.error && !r.pending).length,
    unreadable: rs.filter((r) => r.error).length,
    pending: rs.filter((r) => r.pending).length,
  });

  /**
   * Write the JSON report *before* any stdout use — a run whose stdout/stderr pipes
   * went away (detached launcher session) died mid-print and never reached the write
   * at the old bottom position. In `--batch` mode this also fires after every chunk,
   * so a crash never loses what has already been scanned.
   */
  const writeReport = (rs, done, total) => {
    if (!opts.json) return;
    fs.writeFileSync(
      path.resolve(opts.json),
      JSON.stringify(
        {
          method: opts.batch ? 'lean-batch' : opts.precise ? 'lean' : 'lean.js',
          scanned: rs.filter((r) => !r.pending).length,
          done,
          total,
          counts: counts(rs),
          results: rs,
        },
        null,
        2,
      ),
    );
  };

  if (opts.batch) {
    const toEntry = (f, fallbackFile) => {
      if (!f || f.error) {
        return {
          file: f?.file || fallbackFile,
          method: 'lean-batch',
          ok: false,
          error: f?.error || 'no result',
        };
      }
      try {
        return checkFromJson(f.file, f.json);
      } catch (e) {
        return {
          file: f.file,
          method: 'lean-batch',
          ok: false,
          error: String(e?.message || e).split('\n')[0],
        };
      }
    };
    // Input-aligned `fetched` slots still `undefined` are modules not probed yet.
    const convert = (fetched, done, total) => {
      const rs = fetched.map((f, i) =>
        f === undefined
          ? { file: relLemma(files[i]), method: 'lean-batch', ok: false, pending: true }
          : toEntry(f, relLemma(files[i])),
      );
      writeReport(rs, done, total);
      return rs;
    };
    const fetched = fetchLemmaJsonBatch(files, {
      chunkSize: opts.chunkSize,
      onChunk: (done, total) => process.stderr.write(`\r… ${done}/${total} modules via Lean`),
      onResults: (soFar, done, total) => convert(soFar, done, total),
    });
    process.stderr.write('\n');
    results.push(...convert(fetched, files.length, files.length));
  } else {
    await runSequential(files, opts, results);
  }

  writeReport(results, results.length, results.length);

  const bad = results.filter((r) => !r.ok && !r.error);
  const unreadable = results.filter((r) => r.error);
  for (const r of opts.all ? results : results.filter((r) => !r.ok)) {
    printResult(r, opts.all && !r.ok);
  }

  const method = opts.batch
    ? 'lean Name.toJson (batched)'
    : opts.precise
      ? 'lean Name.toJson'
      : 'lean.js AST';
  const secs = ((Date.now() - started) / 1000).toFixed(1);
  console.log(
    `\nscanned ${results.length} lemma(s) with ${method} in ${secs}s — ` +
      `${results.length - bad.length - unreadable.length} consistent, ` +
      `${bad.length} inconsistent, ${unreadable.length} unreadable`,
  );
  console.log(
    'inspect one file: node mjs/suggestLemmaPath.mjs <file>   (--precise ⇔ node mjs/suggestFromLean.mjs <file>)',
  );
  if (!opts.precise && !opts.batch) {
    console.log(
      'note: lean.js AST mode is a rough heuristic (it flags most of this tree) — use ' +
        '--batch for the Lean-elaborated verdict over the whole tree.',
    );
  }

  if (bad.length || unreadable.length) process.exitCode = 1;
}

main().catch((e) => {
  console.error(e.message || e);
  process.exit(1);
});
