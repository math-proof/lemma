#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { getMysqlPool } from './lean/fetchLemmaMysql.mjs';
import { REPO_ROOT, isValidModuleName, moduleToLeanPath } from './lean/modulePath.mjs';

async function findModules(pool, pattern) {
  const [rows] = await pool.execute(
    `SELECT l.module, COUNT(*) AS matches
       FROM fingerprint f JOIN lemma l ON l.id = f.id
      WHERE CAST(f.fingerprint AS CHAR CHARACTER SET utf8mb4) COLLATE utf8mb4_bin REGEXP ?
      GROUP BY l.module ORDER BY l.module`,
    [pattern],
  );
  return rows;
}

function printMatches(label, rows) {
  console.log(label + ' (' + rows.length + ' modules)');
  for (const row of rows) console.log(row.module + ' (' + row.matches + ' fingerprints)');
}

async function main() {
  const [flag, pattern, ...extra] = process.argv.slice(2);
  if (flag === '--help') {
    console.log('Usage: node mjs/repair.mjs --input <fingerprint-regex>');
    return;
  }
  if (flag !== '--input' || !pattern || extra.length) {
    throw new Error('Usage: node mjs/repair.mjs --input <fingerprint-regex>');
  }
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
