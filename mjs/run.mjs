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
import { fileURLToPath } from 'url';
import mysql from 'mysql2/promise';
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
  const [result] = await conn.query(
    `REPLACE INTO lemma
      (user, module, imports, \`open\`, set_option, \`def\`, lemma, error, date)
     VALUES (?, ?, CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON), CAST(? AS JSON))`,
    [
      USER,
      module,
      jsonCol(code.imports ?? []),
      jsonCol(code.open ?? []),
      jsonCol(code.set_option ?? []),
      jsonCol(code.def ?? []),
      jsonCol(code.lemma ?? []),
      jsonCol(code.error ?? []),
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

async function main() {
  const args = process.argv.slice(2).filter((a) => a !== '--');
  if (args.length === 0 || args.includes('-h') || args.includes('--help')) {
    console.error('usage: node mjs/run.mjs <lean-file-or-module>');
    process.exit(args.length === 0 ? 2 : 0);
  }

  const { module, abs } = await runLeanFile(args[0]);
  console.log(`replaced axiom.lemma user=${USER} module=${module}`);
  console.log(abs);
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(fileURLToPath(import.meta.url))) {
  main().catch((e) => {
    console.error(e.message || e);
    process.exit(1);
  });
}
