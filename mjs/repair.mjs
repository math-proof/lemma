#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { getMysqlPool } from './lean/fetchLemmaMysql.mjs';
import { REPO_ROOT, isValidModuleName, moduleToLeanPath } from './lean/modulePath.mjs';
import { fingerprintMatches, parseFingerprintPattern, patternHeads } from './lean/fingerprintPattern.mjs';

const USAGE = 'Usage: node mjs/repair.mjs --json <json-fingerprint>';

function likeLiteral(text) {
  return '%' + String(text).replace(/[\\%_]/g, (ch) => '\\' + ch) + '%';
}

function fingerprintTree(value) {
  if (value == null || typeof value === 'object') return value;
  if (typeof value !== 'string') return null;
  const text = value.trim();
  if (!text.startsWith('{') && !text.startsWith('[')) return null;
  try {
    return JSON.parse(text);
  } catch {
    return null;
  }
}

/**
 * Subtree search. `"_"` matches one subtree, so `{"Pow":["_","2"]}` is Pow(_2).
 * `"/[2-4]/"` matches a string leaf in that range. `$n` is a repeated hole.
 * The pattern matches anywhere inside a stored fingerprint.
 */
async function findModules(pool, pattern) {
  const heads = patternHeads(pattern);
  const where = heads.map(() => 'CAST(f.fingerprint AS CHAR) LIKE ? ESCAPE \'\\\\\'').join(' AND ');
  const [rows] = await pool.execute(
    `SELECT l.module, f.fingerprint
       FROM fingerprint f JOIN lemma l ON l.id = f.id
      ${where ? 'WHERE ' + where : ''}`,
    heads.map(likeLiteral),
  );
  const counts = new Map();
  for (const row of rows) {
    const tree = fingerprintTree(row.fingerprint);
    if (!fingerprintMatches(pattern, tree)) continue;
    counts.set(row.module, (counts.get(row.module) ?? 0) + 1);
  }
  return [...counts.entries()]
    .sort((a, b) => (a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0))
    .map(([module, matches]) => ({ module, matches }));
}

function printMatches(label, rows) {
  console.log(label + ' (' + rows.length + ' modules)');
  for (const row of rows) console.log(row.module + ' (' + row.matches + ' fingerprints)');
}

async function main() {
  const [flag, raw, ...extra] = process.argv.slice(2);
  if (flag === '--help') {
    console.log(USAGE);
    return;
  }
  if (flag !== '--json' || !raw || extra.length) {
    throw new Error(USAGE);
  }
  const pattern = parseFingerprintPattern(raw);
  const pool = getMysqlPool();
  if (!pool) throw new Error('MySQL is not configured');
  try {
    const before = await findModules(pool, pattern);
    printMatches('Modules to rebuild', before);
    const runner = fileURLToPath(new URL('./run.mjs', import.meta.url));
    let failures = 0;
    for (const { module } of before) {
      if (!isValidModuleName(module)) {
        console.error('Cannot rebuild invalid module ' + module);
        failures++;
        continue;
      }
      console.log('Rebuilding ' + module);
      const result = spawnSync(process.execPath, [runner, moduleToLeanPath(module)], {
        cwd: REPO_ROOT, stdio: 'inherit',
      });
      if (result.status !== 0) {
        failures++;
        console.error('Rebuild failed for ' + module + ': ' + (result.error?.message ?? result.signal ?? result.status));
      }
    }
    const after = await findModules(pool, pattern);
    printMatches('Remaining matches', after);
    console.log('Failed rebuilds: ' + failures);
    if (failures || after.length) process.exitCode = 1;
  } finally {
    await pool.end();
  }
}

main().catch(error => {
  console.error(error.message);
  process.exitCode = 1;
});
