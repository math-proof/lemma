/**
 * Re-run mjs/run.mjs for axiom.lemma rows whose proof LaTeX is not ready.
 *
 * Ready rules:
 * - proof with exactly one {lean,latex} step and no latex → ready (by design)
 * - multi-step with all latex filled, or only a single trailing null → ready
 * - empty lemma JSON, or multi-step with mid-proof missing latex → not ready
 *
 *   node mjs/run_missing_latex.mjs
 *   node mjs/run_missing_latex.mjs --dry-run
 *   node mjs/run_missing_latex.mjs --only-missing-latex   # skip empty lemma arrays
 *   node mjs/run_missing_latex.mjs --limit 20
 *   node mjs/run_missing_latex.mjs --concurrency 1
 */
import fs from 'fs';
import path from 'path';
import mysql from 'mysql2/promise';
import { runLeanFile } from './run.mjs';
import { moduleToLeanPath, fileExists } from '../server/lean/modulePath.mjs';

const USER = process.env.LEAN_PROJECT_USER || path.basename(process.cwd());

function latexReady(lx) {
  if (lx == null || lx === '') return false;
  if (Array.isArray(lx)) {
    return lx.length > 0 && lx.every((x) => x != null && String(x).length > 0);
  }
  return String(lx).length > 0;
}

function proofSteps(lem) {
  const hits = [];
  function walk(n) {
    if (!n) return;
    if (Array.isArray(n)) return n.forEach(walk);
    if (typeof n !== 'object') return;
    if (
      Object.prototype.hasOwnProperty.call(n, 'lean') &&
      Object.prototype.hasOwnProperty.call(n, 'latex')
    ) {
      hits.push(n);
      return;
    }
    for (const [k, v] of Object.entries(n)) {
      if (k === 'lean' || k === 'latex') continue;
      walk(v);
    }
  }
  walk(lem);
  return hits;
}

export function needsLatexRun(lem) {
  if (!Array.isArray(lem) || lem.length === 0) {
    return { need: true, reason: 'empty_lemma' };
  }
  const steps = proofSteps(lem);
  if (steps.length === 0) return { need: true, reason: 'no_proof_steps' };
  // One lean statement in the proof → no latex expected.
  if (steps.length === 1) {
    return { need: false, reason: 'ok_single_step_no_latex' };
  }
  const badIdx = [];
  for (let i = 0; i < steps.length; i++) {
    if (!latexReady(steps[i].latex)) badIdx.push(i);
  }
  if (badIdx.length === 0) return { need: false, reason: 'ok' };
  if (badIdx.length === 1 && badIdx[0] === steps.length - 1) {
    return { need: false, reason: 'ok_trailing_null', steps: steps.length };
  }
  return {
    need: true,
    reason: 'missing_latex',
    steps: steps.length,
    bad: badIdx.length,
    ready: steps.length - badIdx.length,
  };
}

function parseArgs(argv) {
  const opts = {
    dryRun: false,
    onlyMissingLatex: false,
    limit: Infinity,
    concurrency: 1,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--dry-run') opts.dryRun = true;
    else if (a === '--only-missing-latex') opts.onlyMissingLatex = true;
    else if (a === '--limit') opts.limit = Number(argv[++i]);
    else if (a === '--concurrency') opts.concurrency = Math.max(1, Number(argv[++i]) || 1);
    else if (a === '-h' || a === '--help') opts.help = true;
  }
  return opts;
}

async function connectMysql() {
  const host = (process.env.MYSQL_HOST || '127.0.0.1').trim();
  const port = Number(process.env.MYSQL_PORT || 3306);
  const candidates = [
    { host, port, database: 'axiom', user: 'prod', password: 'prod' },
    { host, port, database: 'axiom', user: 'user', password: 'user' },
  ];
  let last = null;
  for (const cfg of candidates) {
    try {
      return await mysql.createConnection({ ...cfg, charset: 'utf8mb4' });
    } catch (e) {
      last = e;
    }
  }
  throw last ?? new Error('mysql connect failed');
}

async function listNeed(opts) {
  const conn = await connectMysql();
  try {
    const [rows] = await conn.query(`SELECT module, lemma FROM lemma WHERE user = ?`, [USER]);
    const need = [];
    for (const r of rows) {
      const d = needsLatexRun(r.lemma);
      if (!d.need) continue;
      if (opts.onlyMissingLatex && d.reason === 'empty_lemma') continue;
      const abs = moduleToLeanPath(r.module);
      if (!abs || !fileExists(abs)) continue;
      need.push({ module: r.module, file: abs, ...d });
    }
    return need;
  } finally {
    await conn.end();
  }
}

async function mapPool(items, concurrency, fn) {
  let i = 0;
  const results = new Array(items.length);
  async function worker() {
    while (i < items.length) {
      const idx = i++;
      results[idx] = await fn(items[idx], idx);
    }
  }
  await Promise.all(Array.from({ length: Math.min(concurrency, items.length) }, () => worker()));
  return results;
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  if (opts.help) {
    console.log(`usage: node mjs/run_missing_latex.mjs [--dry-run] [--only-missing-latex] [--limit N] [--concurrency N]`);
    process.exit(0);
  }

  let need = await listNeed(opts);
  need.sort((a, b) => {
    const rank = (r) => (r === 'missing_latex' ? 0 : r === 'no_proof_steps' ? 1 : 2);
    return rank(a.reason) - rank(b.reason) || a.module.localeCompare(b.module);
  });
  if (Number.isFinite(opts.limit)) need = need.slice(0, opts.limit);

  const byReason = need.reduce((a, x) => ((a[x.reason] = (a[x.reason] || 0) + 1), a), {});
  console.log(`need=${need.length} reasons=${JSON.stringify(byReason)} dryRun=${opts.dryRun} concurrency=${opts.concurrency}`);

  const logPath = path.join('mjs', `_run_missing_latex_${new Date().toISOString().replace(/[:.]/g, '-')}.log`);
  const log = (line) => {
    const s = `[${new Date().toISOString()}] ${line}`;
    console.log(s);
    fs.appendFileSync(logPath, s + '\n');
  };
  log(`start need=${need.length}`);

  if (opts.dryRun) {
    for (const x of need.slice(0, 50)) log(`DRY ${x.reason} ${x.module}`);
    if (need.length > 50) log(`DRY ... +${need.length - 50} more`);
    process.exit(0);
  }

  let ok = 0;
  let fail = 0;
  await mapPool(need, opts.concurrency, async (item, idx) => {
    const n = idx + 1;
    log(`(${n}/${need.length}) RUN ${item.module} [${item.reason}]`);
    try {
      await runLeanFile(item.module);
      ok++;
      log(`(${n}/${need.length}) OK  ${item.module}`);
    } catch (e) {
      fail++;
      log(`(${n}/${need.length}) FAIL ${item.module} :: ${e?.message || e}`);
    }
  });

  log(`done ok=${ok} fail=${fail} total=${need.length} log=${logPath}`);
}

if (process.argv[1] && path.resolve(process.argv[1]).endsWith('run_missing_latex.mjs')) {
  main().catch((e) => {
    console.error(e);
    process.exit(1);
  });
}
