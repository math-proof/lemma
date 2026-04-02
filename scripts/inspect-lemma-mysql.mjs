/**
 * Dump proof.by[].latex from MySQL for a module (requires MYSQL_HOST, etc.).
 * Usage: MYSQL_HOST=127.0.0.1 node scripts/inspect-lemma-mysql.mjs [module] [user]
 */
import {
  getMysqlConfig,
  fetchLemmaRowFromMysql,
  codeFromMysqlRow,
} from '../server/lean/fetchLemmaMysql.mjs';
import path from 'path';
import { fileURLToPath } from 'url';

const moduleArg =
  process.argv[2] || 'Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax';
const repoRoot = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');
const userArg =
  process.argv[3] || process.env.LEAN_PROJECT_USER || path.basename(repoRoot);

const cfg = getMysqlConfig();
if (!cfg) {
  console.error('No MYSQL_HOST — set MYSQL_HOST (and MYSQL_USER / MYSQL_PWD / MYSQL_DATABASE if needed).');
  process.exit(2);
}

const row = await fetchLemmaRowFromMysql(userArg, moduleArg);
if (!row) {
  console.error(`No row for user=${JSON.stringify(userArg)} module=${JSON.stringify(moduleArg)}`);
  process.exit(1);
}

const code = codeFromMysqlRow(row, moduleArg, userArg);
console.log('--- row keys:', Object.keys(row));
console.log('--- codeFromMysqlRow ok:', !!code);

function walkLemma(lemma) {
  if (!Array.isArray(lemma)) {
    console.log('lemma is not an array:', typeof lemma);
    return;
  }
  for (let i = 0; i < lemma.length; i++) {
    const L = lemma[i];
    const proof = L?.proof;
    if (!proof) continue;
    const by = proof.by ?? proof.calc ?? proof;
    if (!Array.isArray(by)) continue;
    console.log(`\n--- lemma[${i}] proof steps: ${by.length}`);
    for (let j = 0; j < by.length; j++) {
      const step = by[j];
      const latex = step?.latex;
      const preview =
        typeof latex === 'string'
          ? latex.slice(0, 120) + (latex.length > 120 ? '…' : '')
          : String(latex);
      console.log(`  [${j}] latex (${typeof latex}): ${preview}`);
    }
  }
}

if (code?.lemma) walkLemma(code.lemma);
else {
  console.log('Raw row.lemma type:', typeof row.lemma);
  let raw = row.lemma;
  if (typeof raw === 'string') {
    try {
      raw = JSON.parse(raw);
    } catch (e) {
      console.error('JSON.parse(lemma) failed:', e.message);
    }
  }
  walkLemma(raw);
}

process.exit(0);
