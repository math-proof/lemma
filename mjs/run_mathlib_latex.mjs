#!/usr/bin/env node
/**
 * Batch-generate LaTeX/JSON (imply) for mathlib theorems whose `imply` column
 * is empty. Queries MySQL for unbuilt theorems, writes a temp .lean file that
 * calls Name.toJson on each, runs `lake env lean` once per batch, parses the
 * JSONL output, and REPLACEs into the mathlib table.
 *
 *   node mjs/run_mathlib_latex.mjs
 *   node mjs/run_mathlib_latex.mjs --limit 100
 *   node mjs/run_mathlib_latex.mjs --batch 200 --concurrency 2
 *   node mjs/run_mathlib_latex.mjs --dry-run
 *   MYSQL_PWD=xxx USER=Administrator node mjs/run_mathlib_latex.mjs
 *
 * Each batch takes ~10-20s (5s Lean startup + ~35ms per theorem parsing).
 * For 306k theorems at 200/batch: ~1500 batches × 15s ≈ 6h single-threaded.
 */
import fs from 'fs';
import path from 'path';
import { execFileSync } from 'child_process';
import { fileURLToPath } from 'url';
import mysql from 'mysql2/promise';

const REPO_ROOT = process.cwd();
const BATCH_LEAN = path.join(REPO_ROOT, 'test.mathlib_batch.lean');
const LAKE = path.join(process.env.HOME || '', '.elan', 'bin', 'lake');

const TEXT_COLS = ['type', 'instImplicit', 'strictImplicit', 'implicit', 'default'];
const JSON_COLS = ['given', 'imply'];

function parseArgs(argv) {
  const opts = { limit: Infinity, batch: 200, concurrency: 1, dryRun: false };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--dry-run') opts.dryRun = true;
    else if (a === '--limit') opts.limit = Number(argv[++i]);
    else if (a === '--batch') opts.batch = Number(argv[++i]);
    else if (a === '--concurrency') opts.concurrency = Math.max(1, Number(argv[++i]) || 1);
    else if (a === '-h' || a === '--help') opts.help = true;
  }
  return opts;
}

async function connectMysql() {
  const host = (process.env.MYSQL_HOST || '127.0.0.1').trim();
  const port = Number(process.env.MYSQL_PORT || 3306);
  const candidates = [];
  if (process.env.MYSQL_PWD != null) {
    candidates.push({
      host, port, database: 'axiom',
      user: process.env.USER || process.env.USERNAME || 'prod',
      password: process.env.MYSQL_PWD,
    });
  }
  candidates.push({ host, port, database: 'axiom', user: 'prod', password: 'prod' });
  candidates.push({ host, port, database: 'axiom', user: 'user', password: 'user' });
  candidates.push({ host, port, database: 'axiom', user: 'Administrator', password: '' });
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

async function listUnbuilt(conn, limit) {
  const sql = `SELECT name FROM mathlib
     WHERE imply IS NULL OR imply = '{}' OR JSON_LENGTH(imply) = 0
        OR JSON_EXTRACT(imply, '$.latex') IS NULL
        OR JSON_EXTRACT(imply, '$.latex') = ''
        OR JSON_EXTRACT(imply, '$.latex') = 'null'
     ORDER BY RAND()`;
  const query = Number.isFinite(limit) ? `${sql} LIMIT ?` : sql;
  const params = Number.isFinite(limit) ? [limit] : [];
  const [rows] = await conn.query(query, params);
  return rows.map((r) => r.name);
}

function generateBatchLean(names) {
  const namesArr = names.map((n) => JSON.stringify(n)).join(', ');
  return `import Mathlib
import sympy.printing.json
open Lean Meta
#eval Meta.MetaM.run' do
  let names := [${namesArr}]
  for s in names do
    let name := s.splitOn "." |>.foldl (fun acc n => Name.mkStr acc n) Name.anonymous
    try
      println! s!"{Json.compress (← Name.toJson name)}"
    catch _ =>
      println! s!"{Json.compress (Json.mkObj [("name", s), ("error", true)])}"
`;
}

function runBatch(names) {
  const code = generateBatchLean(names);
  fs.writeFileSync(BATCH_LEAN, code);

  let output;
  try {
    output = execFileSync(LAKE, ['env', 'lean', BATCH_LEAN], {
      cwd: REPO_ROOT,
      encoding: 'utf8',
      timeout: 600000,
      maxBuffer: 100 * 1024 * 1024,
      stdio: ['pipe', 'pipe', 'pipe'],
    });
  } catch (e) {
    // attach stderr for diagnostics, keep temp file for debugging
    const stderr = e.stderr ? e.stderr.toString() : '';
    const stdout = e.stdout ? e.stdout.toString() : '';
    e.message = `${e.message}\n--- stderr ---\n${stderr}\n--- stdout ---\n${stdout.slice(0, 2000)}\n--- lean file kept at ${BATCH_LEAN}`;
    throw e;
  }

  if (fs.existsSync(BATCH_LEAN)) fs.unlinkSync(BATCH_LEAN);

  const results = [];
  for (const line of output.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed || !trimmed.startsWith('{')) continue;
    try {
      results.push(JSON.parse(trimmed));
    } catch {
      // skip non-JSON lines (warnings, info messages)
    }
  }
  return results;
}

async function updateMathlibRow(conn, json) {
  const name = json.name;
  if (!name) return false;

  const vals = [name];
  for (const col of TEXT_COLS) {
    vals.push(typeof json[col] === 'string' ? json[col] : null);
  }
  // given and imply are JSON columns
  vals.push(json.given != null ? JSON.stringify(json.given) : null);
  vals.push(json.imply != null ? JSON.stringify(json.imply) : '{}');

  await conn.query(
    `REPLACE INTO mathlib
      (name, type, instImplicit, strictImplicit, implicit, \`default\`, given, imply)
     VALUES (?, ?, ?, ?, ?, ?, CAST(? AS JSON), CAST(? AS JSON))`,
    vals,
  );
  return true;
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
    console.log(`usage: node mjs/run_mathlib_latex.mjs [--limit N] [--batch N] [--concurrency N] [--dry-run]`);
    process.exit(0);
  }

  const conn = await connectMysql();
  try {
    const names = await listUnbuilt(conn, opts.limit);
    if (names.length === 0) {
      console.log('no unbuilt theorems found');
      return;
    }
    console.log(`unbuilt: ${names.length} batch=${opts.batch} concurrency=${opts.concurrency} dryRun=${opts.dryRun}`);

    // partition into batches
    const batches = [];
    for (let i = 0; i < names.length; i += opts.batch) {
      batches.push(names.slice(i, i + opts.batch));
    }

    if (opts.dryRun) {
      for (const b of batches.slice(0, 5)) {
        console.log(`DRY batch (${b.length}): ${b.slice(0, 3).join(', ')}${b.length > 3 ? ' ...' : ''}`);
      }
      if (batches.length > 5) console.log(`DRY ... +${batches.length - 5} more batches`);
      return;
    }

    const logPath = path.join('mjs', `_run_mathlib_latex_${new Date().toISOString().replace(/[:.]/g, '-')}.log`);
    const log = (line) => {
      const s = `[${new Date().toISOString()}] ${line}`;
      console.log(s);
      fs.appendFileSync(logPath, s + '\n');
    };
    log(`start batches=${batches.length} total=${names.length}`);

    let ok = 0;
    let fail = 0;
    let batchIdx = 0;

    await mapPool(batches, opts.concurrency, async (batch) => {
      const n = ++batchIdx;
      const t0 = Date.now();
      try {
        const results = runBatch(batch);
        let batchOk = 0;
        let batchFail = 0;
        for (const json of results) {
          if (json.error) {
            batchFail++;
            continue;
          }
          await updateMathlibRow(conn, json);
          batchOk++;
        }
        // theorems that didn't produce output (parse failure) count as failed
        const missing = batch.length - results.length;
        if (missing > 0) batchFail += missing;
        ok += batchOk;
        fail += batchFail;
        const dt = ((Date.now() - t0) / 1000).toFixed(1);
        log(`(${n}/${batches.length}) ${dt}s ok=${batchOk} fail=${batchFail} (${batch[0]}…)`);
      } catch (e) {
        fail += batch.length;
        const dt = ((Date.now() - t0) / 1000).toFixed(1);
        log(`(${n}/${batches.length}) ${dt}s ERROR: ${e?.message || e} (${batch[0]}…)`);
      }
    });

    log(`done ok=${ok} fail=${fail} total=${names.length} log=${logPath}`);
  } finally {
    await conn.end();
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url))) {
  main().catch((e) => {
    console.error(e);
    process.exit(1);
  });
}
