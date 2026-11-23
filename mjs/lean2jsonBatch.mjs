#!/usr/bin/env node
import fs from 'node:fs/promises';
import path from 'node:path';
import { getMysqlPool } from './lean/fetchLemmaMysql.mjs';
import { REPO_ROOT } from './lean/modulePath.mjs';
import { fingerprintFormat, fingerprintSignature, parseFingerprint, refreshInvertedForLemma } from './leanInvertedIndex.mjs';
import { buildEcho, probeLemma } from './lean2json.mjs';

const DEFAULT_STATE = path.join(REPO_ROOT, 'tmp', 'lean2json-batch.jsonl');
const DEFAULT_REPORT = path.join(REPO_ROOT, 'tmp', 'lean2json-failures.json');

/**
 * Probe every lemma that has a fingerprint in MySQL and compare the stored
 * fingerprint with the one converted from Lean's `Expr.toJson`.
 *
 * - stored == struct            -> ok
 * - stored != source            -> the row is stale: rebuild it incrementally,
 *                                  re-read it, and compare again (rebuilt / rebuilt-mismatch)
 * - stored == source != struct  -> the row matches the current source parse (the
 *                                  authority), so the struct cannot reproduce it:
 *                                  reported as a reasonable provenance mismatch
 *
 * Results are appended to a JSONL state file after every lemma, so an
 * interrupted run resumes where it stopped.
 */

function parseArgs(argv) {
  const options = { limit: Infinity, state: DEFAULT_STATE, report: DEFAULT_REPORT, reset: false };
  for (let i = 0; i < argv.length; i++) {
    const arg = argv[i];
    if (arg === '--limit') options.limit = Number(argv[++i]);
    else if (arg === '--state') options.state = path.resolve(argv[++i]);
    else if (arg === '--report') options.report = path.resolve(argv[++i]);
    else if (arg === '--reset') options.reset = true;
    else if (arg === '--help') options.help = true;
    else throw new Error('Unknown argument: ' + arg);
  }
  if (options.limit !== Infinity && (!Number.isInteger(options.limit) || options.limit < 0)) {
    throw new Error('--limit needs a non-negative integer');
  }
  return options;
}

async function loadState(file) {
  const seen = new Map();
  let text;
  try {
    text = await fs.readFile(file, 'utf8');
  } catch (err) {
    if (err.code === 'ENOENT') return seen;
    throw err;
  }
  for (const line of text.split('\n')) {
    if (!line.trim()) continue;
    const item = JSON.parse(line);
    if (item?.module) seen.set(item.module, item);
  }
  return seen;
}

async function appendState(file, item) {
  await fs.mkdir(path.dirname(file), { recursive: true });
  await fs.appendFile(file, JSON.stringify(item) + '\n');
}

function classifyError(error) {
  if (error?.code === 'ENOENT') return 'missing';
  if (error?.probe) return 'unsupported';
  return 'error';
}

function shortMessage(error) {
  return String(error?.message ?? '').split('\n')[0].slice(0, 300);
}

async function storedFingerprint(pool, id) {
  const [rows] = await pool.execute("SELECT JSON_EXTRACT(meta, '$.fingerprint') AS fingerprint FROM lemma WHERE id = ?", [id]);
  return parseFingerprint(rows[0]?.fingerprint);
}

async function checkOne(pool, lean, row) {
  const at = new Date().toISOString();
  let result;
  try {
    result = await probeLemma(row.module, { pool, lean });
  } catch (error) {
    return { module: row.module, at, status: classifyError(error), message: shortMessage(error) };
  }

  const views = {
    path: result.path,
    stored: fingerprintFormat(result.stored),
    storedLean: result.sourceLean,
    source: fingerprintFormat(result.sourceJson),
    struct: fingerprintFormat(result.structJson),
  };
  if (result.structMatchesStored) return { module: row.module, at, status: 'ok', ...views };
  if (result.sourceMatchesStored) {
    // The row agrees with the current source parse, so a rebuild would change
    // nothing; the divergence lives in the struct -> fingerprint conversion.
    return { module: row.module, at, status: 'mismatch', ...views, exprToJson: result.echo.struct };
  }

  // Stale row: replace its fingerprint and postings incrementally, then test afresh.
  const rebuild = await refreshInvertedForLemma(pool, {
    id: row.id,
    module: row.module,
    json: result.sourceJson,
    startedAt: Date.now(),
  });
  if (rebuild.stale || rebuild.missing) {
    return { module: row.module, at, status: 'error', message: 'rebuild skipped: ' + JSON.stringify(rebuild), ...views };
  }
  const stored = await storedFingerprint(pool, row.id);
  if (fingerprintSignature(stored) !== fingerprintSignature(result.sourceJson)) {
    return { module: row.module, at, status: 'error', message: 'source changed during rebuild', ...views };
  }
  const refined = fingerprintFormat(stored);
  if (fingerprintSignature(result.structJson) === fingerprintSignature(stored)) {
    return { module: row.module, at, status: 'rebuilt', ...views, stored: refined };
  }
  return {
    module: row.module,
    at,
    status: 'rebuilt-mismatch',
    ...views,
    stored: refined,
    exprToJson: result.echo.struct,
  };
}

function failureEntry(item) {
  return {
    module: item.module,
    path: item.path ?? null,
    storedFingerprint: item.stored,
    exprToJson: item.exprToJson ?? null,
    convertedFingerprint: item.struct,
  };
}

export async function writeFailureReport(file, failures) {
  await fs.mkdir(path.dirname(file), { recursive: true });
  await fs.writeFile(file, JSON.stringify({
    generatedAt: new Date().toISOString(),
    count: failures.length,
    failures: failures.map(failureEntry),
  }, null, 2) + '\n');
}

/** One markdown file per lemma, mirroring the module hierarchy under `dir`. */
function markdownPath(dir, module) {
  const parts = module.split('.').map(part => part.replace(/[^A-Za-z0-9_'-]/g, '_'));
  return path.join(dir, ...parts) + '.md';
}

function statusNote(item) {
  if (item.status === 'rebuilt-mismatch') {
    return '`rebuilt-mismatch` — the stale row was rebuilt and now matches the JS parse; the conversion still differs';
  }
  return '`mismatch` — the stored fingerprint matches the JS parse, so the conversion is the source of the difference';
}

/**
 * Pretty-print an `Expr.toJson` node with `op`/`kind` first, scalar fields
 * grouped on one line, and `args` last, so a node reads top-down instead of
 * exposing the raw insertion order (`args` first).
 */
function formatExpr(node, pad = '') {
  const next = pad + '  ';
  if (node === null || typeof node !== 'object') return JSON.stringify(node);
  if (Array.isArray(node)) {
    if (node.length === 0) return '[]';
    return '[\n' + node.map(item => next + formatExpr(item, next)).join(',\n') + '\n' + pad + ']';
  }
  const keys = Object.keys(node);
  const ordered = [
    ...['op', 'kind'].filter(key => key in node),
    ...keys.filter(key => key !== 'op' && key !== 'kind' && key !== 'args'),
    ...keys.filter(key => key === 'args'),
  ];
  const scalars = ordered.filter(key => node[key] === null || typeof node[key] !== 'object');
  const nested = ordered.filter(key => node[key] !== null && typeof node[key] === 'object');
  const lines = [];
  if (scalars.length) {
    lines.push(scalars.map(key => `${JSON.stringify(key)}: ${JSON.stringify(node[key])}`).join(', '));
  }
  for (const key of nested) {
    const value = node[key];
    if (Array.isArray(value) && value.length === 0) {
      lines.push(`${JSON.stringify(key)}: []`);
    } else if (Array.isArray(value)) {
      const items = value.map(item => next + '  ' + formatExpr(item, next + '  '));
      lines.push(`${JSON.stringify(key)}: [\n${items.join(',\n')}\n${next}]`);
    } else {
      lines.push(`${JSON.stringify(key)}: ${formatExpr(value, next)}`);
    }
  }
  if (lines.length === 0) return '{}';
  return '{\n' + lines.map(line => next + line).join(',\n') + '\n' + pad + '}';
}

function leanBlock(text) {
  return text == null || text === '' ? '_not captured_' : '```lean\n' + text + '\n```';
}

function markdownFor(item) {
  const file = item.path ? `[${path.basename(item.path)}](file://${item.path})` : '_unknown_';
  const raw = item.exprToJson == null
    ? '_not captured_'
    : '```json\n' + formatExpr(item.exprToJson) + '\n```';
  return [
    `# ${item.module}`,
    '',
    `- **Lemma file:** ${file}`,
    `- **Path:** \`${item.path}\``,
    `- **Status:** ${statusNote(item)}`,
    '',
    '## Lean expression',
    '',
    leanBlock(item.storedLean),
    '',
    '## Stored fingerprint (from MySQL)',
    '',
    '```',
    item.stored,
    '```',
    '',
    '## Converted fingerprint (`Expr.toJson` via `structToFingerprint`)',
    '',
    '```',
    item.struct,
    '```',
    '',
    '## Raw `Expr.toJson`',
    '',
    raw,
    '',
  ].join('\n');
}

/** Write the readable form: `dir/index.md` plus one markdown file per lemma. */
export async function writeFailureMarkdown(dir, failures) {
  await fs.rm(dir, { recursive: true, force: true });
  await fs.mkdir(dir, { recursive: true });
  const rows = [];
  for (const item of failures) {
    const file = markdownPath(dir, item.module);
    await fs.mkdir(path.dirname(file), { recursive: true });
    await fs.writeFile(file, markdownFor(item));
    const rel = path.relative(dir, file).split(path.sep).join('/');
    rows.push(`| ${rows.length + 1} | [${item.module}](./${rel}) | \`${item.status}\` | [${path.basename(item.path ?? '')}](file://${item.path}) |`);
  }
  await fs.writeFile(path.join(dir, 'index.md'), [
    '# lean2json failure report',
    '',
    `Generated ${new Date().toISOString()}`,
    '',
    `**${failures.length}** failure(s), one markdown file per lemma: stored fingerprint, converted fingerprint, and the raw \`Expr.toJson\`.`,
    '',
    '| # | Module | Status | Lemma file |',
    '|---|--------|--------|------------|',
    ...rows,
    '',
  ].join('\n'));
  return dir;
}

function printReport(tally, failures, processed, skipped, reportPath) {
  console.log('');
  console.log(`processed ${processed} lemma(s), skipped ${skipped} already recorded`);
  for (const status of ['ok', 'rebuilt', 'mismatch', 'rebuilt-mismatch', 'unsupported', 'missing', 'error']) {
    if (tally[status]) console.log(`  ${status.padEnd(16)} ${tally[status]}`);
  }
  console.log('');
  console.log(`failure report: ${reportPath} (${failures.length} mismatch(es), includes raw Expr.toJson)`);
  for (const item of failures.slice(0, 5)) {
    console.log('');
    console.log('  ' + item.module + (item.status === 'rebuilt-mismatch' ? '  [row rebuilt]' : ''));
    console.log('    path:   ' + item.path);
    console.log('    stored: ' + item.stored);
    console.log('    struct: ' + item.struct);
    console.log('    Expr.toJson: ' + formatExpr(item.exprToJson).replace(/\n/g, '\n      '));
  }
  if (failures.length > 5) console.log(`\n  ... ${failures.length - 5} more in ${reportPath}`);
  console.log(`readable report: ${reportPath.replace(/\.json$/i, '')}/index.md`);
}

async function main() {
  const options = parseArgs(process.argv.slice(2));
  if (options.help) {
    console.log('Usage: node mjs/lean2jsonBatch.mjs [--limit N] [--state FILE] [--report FILE] [--reset]');
    return;
  }
  if (options.reset) await fs.rm(options.state, { force: true });
  const state = await loadState(options.state);

  const pool = getMysqlPool();
  if (!pool) throw new Error('MySQL is not configured');
  const [rows] = await pool.query(
    "SELECT id, module FROM lemma WHERE JSON_EXTRACT(meta, '$.fingerprint') IS NOT NULL ORDER BY module",
  );
  console.log(`${rows.length} lemma(s) with a fingerprint, ${state.size} already in ${options.state}`);

  const lean = await buildEcho();
  const tally = {};
  let processed = 0;
  let skipped = 0;
  for (const row of rows) {
    if (processed >= options.limit) break;
    if (state.get(row.module)?.status && state.get(row.module).status !== 'error') {
      skipped++;
      continue;
    }
    const item = await checkOne(pool, lean, row);
    await appendState(options.state, item);
    state.set(row.module, item);
    tally[item.status] = (tally[item.status] ?? 0) + 1;
    processed++;
    console.log(`[${processed}] ${item.module} ${item.status}${item.message ? ': ' + item.message : ''}`);
  }
  await pool.end();
  const failures = [...state.values()].filter(item => item.status === 'mismatch' || item.status === 'rebuilt-mismatch');
  await writeFailureReport(options.report, failures);
  await writeFailureMarkdown(options.report.replace(/\.json$/i, ''), failures);
  printReport(tally, failures, processed, skipped, options.report);
  if (tally.error) process.exitCode = 1;
}

main().catch(error => {
  console.error(error.message);
  process.exitCode = 1;
});
