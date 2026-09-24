#!/usr/bin/env node
/**
 * Compile a Lemma/*.lean file (echo tactics → lake env lean → proof LaTeX)
 * and REPLACE the row in axiom.lemma.
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
import '../static/js/std.js';
import { echo2vueFromSource } from '../server/lean/compiler/index.mjs';
import {
  REPO_ROOT,
  leanPathToModule,
  moduleToLeanPath,
  fileExists,
} from '../server/lean/modulePath.mjs';

const USER = process.env.LEAN_PROJECT_USER || path.basename(REPO_ROOT);

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
    const module = leanPathToModule(chosen, REPO_ROOT);
    if (!module) throw new Error(`not under Lemma/: ${chosen}`);
    return { abs: chosen, module };
  }

  const abs = moduleToLeanPath(raw);
  if (!abs) throw new Error(`bad module: ${raw}`);
  return { abs, module: raw };
}

async function replaceLemmaRow(conn, module, code) {
  const errs = Array.isArray(code.error) ? code.error : [];
  const metaJson = errs.length ? jsonCol({ error: errs }) : null;
  const [result] = await conn.query(
    `REPLACE INTO lemma
      (user, module, imports, \`open\`, set_option, preamble, lemma, meta, date)
     VALUES (?, ?, CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON))`,
    [
      USER,
      module,
      jsonCol(code.imports ?? []),
      jsonCol(code.open ?? []),
      jsonCol(code.set_option ?? []),
      jsonCol(code.preamble ?? []),
      jsonCol(code.lemma ?? []),
      metaJson,
      jsonCol(code.date ?? {}),
    ]
  );
  return result;
}

export async function runLeanFile(leanInput) {
  const { abs, module } = resolveLeanFile(leanInput);
  if (!fileExists(abs)) throw new Error(`file not found: ${abs}`);
  const source = fs.readFileSync(abs, 'utf8');
  const code = await echo2vueFromSource(source, { leanAbsPath: abs, module });
  const conn = await connectMysql();
  try {
    await replaceLemmaRow(conn, module, code);
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
    console.error('usage: node mjs/run.mjs <lean-file-or-module>');
    process.exit(0);
  }

  const leanInput = args[0] || (await promptLeanInput());
  if (!leanInput) {
    console.error('usage: node mjs/run.mjs <lean-file-or-module>');
    process.exit(2);
  }

  const { module, abs, code } = await runLeanFile(leanInput);
  console.log(abs);

  // MySQL REPLACE is persistence, not success — Lean errors decide the exit status.
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
      `FAILED: wrote axiom.lemma user=${USER} module=${module} (${errors.length} Lean error(s))`,
    );
    process.exitCode = 1;
  } else {
    console.log(`OK: replaced axiom.lemma user=${USER} module=${module}`);
  }
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url))) {
  main().catch((e) => {
    console.error(e.message || e);
    process.exit(1);
  });
}
