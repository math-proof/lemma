#!/usr/bin/env node
/**
 * Compile a Lemma/*.lean file (echo tactics → lake env lean → proof LaTeX)
 * and REPLACE the row in axiom.lemma. Compile Theorem/ files directly.
 *
 *   node mjs/run.mjs Lemma/Real/GtSqrt_0/of/Gt_0.lean
 *   node mjs/run.mjs Real.GtSqrt_0.of.Gt_0
 */
import fs from 'fs';
import path from 'path';
import readline from 'node:readline/promises';
import { stdin as input, stdout as output } from 'node:process';
import { fileURLToPath } from 'url';
import mysql from 'mysql2/promise';
import '../js/py.js';
import { echo2vueFromSource } from './lean/compiler/index.mjs';
import { applyLintFixes, lintLeanFile } from './lean/lint/index.mjs';
import { get_lake_path, get_lean_env, spawnLakeLean } from './lean/echo2vue.mjs';
import {
  REPO_ROOT,
  leanPathToModule,
  moduleToLeanPath,
  fileExists,
} from './lean/modulePath.mjs';
import { lemmaSearchDocuments } from './lemmaPath.mjs';
import { writeLemmaIndex } from './leanInvertedIndex.mjs';

function jsonCol(v) {
  return JSON.stringify(v ?? (Array.isArray(v) ? [] : {}));
}

async function connectMysql() {
  const host = (process.env.MYSQL_HOST || '127.0.0.1').trim();
  const port = Number(process.env.MYSQL_PORT || 3306);
  const database = 'axiom';
  const candidates = [];
  if (process.env.MYSQL_HOST && process.env.MYSQL_PWD != null) {
    candidates.push({
      host,
      port,
      database,
      user: process.env.USER || process.env.USERNAME || 'prod',
      password: process.env.MYSQL_PWD,
    });
  }
  candidates.push({ host, port, database, user: 'prod', password: 'prod' });
  candidates.push({ host, port, database, user: 'user', password: 'user' });
  let last = null;
  for (const cfg of candidates) {
    try {
      const conn = await mysql.createConnection({ ...cfg, charset: 'utf8mb4' });
      return conn;
    } catch (e) {
      last = e;
    }
  }
  throw last ?? new Error('mysql connect failed');
}

function resolveLeanFile(input) {
  const raw = String(input ?? '').trim();
  if (!raw) throw new Error('missing lean file or module');
  if (raw.endsWith('.echo.lean')) throw new Error(`skip echo sidecar: ${raw}`);

  if (raw.endsWith('.lean') || raw.includes('/') || raw.includes('\\')) {
    const abs = path.isAbsolute(raw)
      ? path.normalize(raw)
      : path.normalize(path.join(process.cwd(), raw));
    const fromRoot = path.normalize(path.join(REPO_ROOT, raw));
    const chosen = fileExists(abs) ? abs : fileExists(fromRoot) ? fromRoot : abs;
    const rel = path.relative(REPO_ROOT, chosen);
    if (rel.startsWith('Theorem' + path.sep) && chosen.endsWith('.lean')) {
      return { abs: chosen, module: rel.slice(0, -5).split(path.sep).join('.'), theorem: true };
    }
    const module = leanPathToModule(chosen, REPO_ROOT);
    if (!module) throw new Error(`not under Lemma/ or Theorem/: ${chosen}`);
    return { abs: chosen, module };
  }

  if (raw.startsWith('Theorem.')) {
    const parts = raw.split('.');
    if (parts.some((part) => !part)) throw new Error(`bad module: ${raw}`);
    const abs = path.join(REPO_ROOT, ...parts) + '.lean';
    return { abs, module: raw, theorem: true };
  }
  const abs = moduleToLeanPath(raw);
  if (!abs) throw new Error(`bad module: ${raw}`);
  return { abs, module: raw };
}

async function replaceLemmaRow(conn, module, code, abs, startedAt) {
  const errs = Array.isArray(code.error) ? code.error : [];
  let fingerprint = null;
  let documents = null;
  try {
    if (abs) {
      const extracted = lemmaSearchDocuments(abs);
      fingerprint = extracted.fingerprint;
      documents = extracted.documents;
    }
  } catch {
    fingerprint = null;
    documents = null;
  }
  const meta = {};
  if (errs.length) meta.error = errs;
  const metaJson = Object.keys(meta).length ? JSON.stringify(meta) : null;

  const fields = [
    jsonCol(code.imports ?? []),
    jsonCol(code.open ?? []),
    jsonCol(code.set_option ?? []),
    jsonCol(code.preamble ?? []),
    jsonCol(code.lemma ?? []),
    metaJson,
    jsonCol(code.date ?? {}),
  ];

  // UNIQUE `uq_lemma_module (module)` keeps `id` stable: UPDATE the existing
  // row in place. INSERT only when the module is new, so inverted postings
  // are not orphaned by a new AUTO_INCREMENT id. The row lock and the
  // fingerprint/postings write share one transaction: a reader sees either
  // the previous revision or the new one, never a half-applied state.
  await conn.beginTransaction();
  try {
    const [existing] = await conn.query(
      "SELECT id, JSON_EXTRACT(meta, '$.revision') AS revision FROM lemma WHERE module = ? FOR UPDATE",
      [module],
    );
    let id;
    if (existing.length) {
      id = existing[0].id;
      // An older job may acquire the lock after a newer build already won.
      if (Number(existing[0].revision ?? 0) > Number(startedAt)) {
        await conn.rollback();
        return { id, stale: true };
      }
      await conn.query(
        `UPDATE lemma
         SET imports = CAST(? AS JSON),
             \`open\` = CAST(? AS JSON),
             set_option = CAST(? AS JSON),
             preamble = CAST(? AS JSON),
             lemma = CAST(? AS JSON),
             meta = CAST(? AS JSON),
             date = CAST(? AS JSON)
         WHERE id = ?`,
        [...fields, id],
      );
    } else {
      const [result] = await conn.query(
        `INSERT INTO lemma
          (module, imports, \`open\`, set_option, preamble, lemma, meta, date)
         VALUES (?, CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON))`,
        [module, ...fields],
      );
      id = result.insertId;
    }

    const { postings } = await writeLemmaIndex(conn, {
      id,
      module,
      json: fingerprint,
      documents,
      startedAt,
    });
    await conn.commit();
    return { id, postings };
  } catch (err) {
    await conn.rollback();
    throw err;
  }
}

export async function runLeanFile(leanInput) {
  const { abs, module, theorem } = resolveLeanFile(leanInput);
  if (!fileExists(abs)) throw new Error(`file not found: ${abs}`);
  // Logical start of this build; stored as meta.revision so a slower, older
  // build that acquires the row lock last can detect that it lost the race.
  const startedAt = Date.now();
  const source = fs.readFileSync(abs, 'utf8');
  if (theorem) {
    const compilation = await spawnLakeLean(get_lake_path(), ['env', 'lean', abs], {
      cwd: REPO_ROOT,
      env: get_lean_env(REPO_ROOT),
    });
    if (compilation.error) throw compilation.error;
    const warning = lintLeanFile(source, abs, { file: path.relative(REPO_ROOT, abs), root: REPO_ROOT });
    return { module, abs, code: { warning }, compilation };
  }
  const code = await echo2vueFromSource(source, { leanAbsPath: abs, module });
  const conn = await connectMysql();
  try {
    await replaceLemmaRow(conn, module, code, abs, startedAt);
  } finally {
    await conn.end();
  }
  return { module, abs, code };
}

async function promptLeanInput() {
  const rl = readline.createInterface({ input, output });
  try {
    return (await rl.question('Lean file path: ')).trim();
  } finally {
    rl.close();
  }
}

async function main() {
  const args = process.argv.slice(2).filter((a) => a !== '--');
  if (args.includes('-h') || args.includes('--help')) {
    console.error('usage: node mjs/run.mjs [--fix] <lean-file-or-module>');
    process.exit(0);
  }
  const fix = args.includes('--fix');

  const leanInput = args.find((a) => !a.startsWith('-')) || (await promptLeanInput());
  if (!leanInput) {
    console.error('usage: node mjs/run.mjs [--fix] <lean-file-or-module>');
    process.exit(2);
  }

  // `--fix`: apply the lint rules' auto-fixes in place and stop (no compile, no MySQL write)
  if (fix) {
    const { abs, module } = resolveLeanFile(leanInput);
    if (!fileExists(abs)) throw new Error(`file not found: ${abs}`);
    const source = fs.readFileSync(abs, 'utf8');
    const { source: fixed, applied } = applyLintFixes(source, { file: module });
    console.log(abs);
    if (fixed === source) {
      console.log('no fixes');
      return;
    }
    fs.writeFileSync(abs, fixed);
    const rules = [...new Set(applied.map((a) => a.rule))].join(', ');
    console.log(`fixed ${applied.length} occurrence(s): ${rules}`);
    const left = applyLintFixes(fixed, { file: module });
    if (left.source !== fixed) console.log(`note: ${left.applied.length} further occurrence(s) need a re-run`);
    return;
  }

  const { module, abs, code, compilation } = await runLeanFile(leanInput);
  console.log(abs);

  // lint warnings (`code.warning`: AGENTS.md style rules, mjs/lean/lint/): printed only — not Lean errors, not saved,
  // no effect on the exit status
  const warnings = Array.isArray(code?.warning) ? code.warning : [];
  for (const w of warnings) {
    const loc = w.line != null ? `:${w.line}${w.col != null ? `:${w.col}` : ''}` : '';
    console.warn(`warning${loc}: ${w.info}`);
    // AST rules quote the offending statement (the parse tree has no positions; search for it by text)
    if (w.stmt) console.warn(w.stmt.split('\n').map((l) => `    > ${l}`).join('\n'));
  }
  if (warnings.length) {
    console.warn(`${warnings.length} style warning(s): fix them and re-run \`node mjs/run.mjs ${leanInput}\` until none remain`);
  }

  if (compilation) {
    if (compilation.stdout) process.stdout.write(compilation.stdout);
    if (compilation.stderr) process.stderr.write(compilation.stderr);
    if (compilation.status === 0) console.log(`OK: compiled ${module}`);
    else process.exitCode = compilation.status || 1;
    return;
  }

  // MySQL write is persistence, not success — Lean errors decide the exit status.
  const errors = Array.isArray(code?.error) ? code.error : [];
  const isCrlf = (e) => /Carriage return/i.test(String(e?.info ?? ''));
  const crlf = errors.filter(isCrlf);
  const real = errors.filter((e) => !isCrlf(e));

  if (crlf.length) {
    console.error(
      `(note: ${crlf.length}× "Carriage return is not allowed in Lean" — convert the .lean file to LF)`,
    );
  }
  if (real.length) {
    console.error(`\n${real.length} Lean error(s):`);
    for (const err of real) {
      const loc = err.line != null ? `:${err.line}` : '';
      const col = err.col != null ? `:${err.col}` : '';
      const typ = err.type || 'error';
      console.error(`--- ${typ}${loc}${col} ---`);
      if (err.code) console.error(err.code);
      if (err.info) console.error(err.info);
    }
  }

  if (errors.length) {
    console.error(
      `FAILED: wrote axiom.lemma module=${module} (${errors.length} Lean error(s))`,
    );
    process.exitCode = 1;
  } else {
    console.log(`OK: replaced axiom.lemma module=${module}`);
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url))) {
  main().catch((e) => {
    console.error(e.message || e);
    process.exit(1);
  });
}
