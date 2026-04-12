/**
 * PHP `lemma.php` `import_syntax` (lines 546–602): before adding a syntax-driven import, check whether
 * some `Lemma.*` import already implies it — first via MySQL recursive `axiom.lemma` deps, then via
 * filesystem `contains_module` on the current import list.
 */
import fs from 'fs';
import path from 'path';
import { REPO_ROOT, moduleToLeanPath } from './modulePath.mjs';
import { getMysqlPool } from './fetchLemmaMysql.mjs';

const TRANSITIVE_IMPORT_MAX_DEPTH = 14;

/** Same recursive shape as `php/lemma.php` lines 555–586 (JSON roots = dotted modules without `Lemma.`). */
const MYSQL_TRANSITIVE_IMPORT_SQL = `
WITH RECURSIVE dependencies AS (
  SELECT jt.module
  FROM JSON_TABLE(?, '$[*]' COLUMNS (module TEXT PATH '$')) AS jt
  UNION ALL
  SELECT SUBSTRING(jt.module, LOCATE('.', jt.module) + 1) AS module
  FROM dependencies AS d
  JOIN axiom.lemma AS _t
    ON BINARY CAST(_t.module AS CHAR CHARACTER SET utf8mb4) = BINARY CAST(d.module AS CHAR CHARACTER SET utf8mb4)
  CROSS JOIN JSON_TABLE(_t.imports, '$[*]' COLUMNS (module TEXT PATH '$')) AS jt
  WHERE jt.module LIKE 'Lemma.%'
)
SELECT COUNT(*) AS cnt
FROM dependencies AS d
JOIN axiom.lemma AS _t
  ON BINARY CAST(_t.module AS CHAR CHARACTER SET utf8mb4) = BINARY CAST(d.module AS CHAR CHARACTER SET utf8mb4)
CROSS JOIN JSON_TABLE(_t.imports, '$[*]' COLUMNS (module TEXT PATH '$')) AS jt
WHERE BINARY CAST(jt.module AS CHAR CHARACTER SET utf8mb4) = BINARY CAST(? AS CHAR CHARACTER SET utf8mb4)
`;

/**
 * @param {string} imp dotted path as in `import` lines, e.g. `Lemma.Tensor.Foo` or `stdlib.SEq`
 * @returns {string | null} absolute `.lean` path under the repo, or null
 */
function resolveImportToLeanPath(imp) {
  const s = String(imp).trim();
  if (!s) return null;
  if (s.startsWith('Lemma.')) {
    return moduleToLeanPath(s.slice('Lemma.'.length));
  }
  for (const root of ['stdlib', 'sympy']) {
    if (s === root || s.startsWith(`${root}.`)) {
      const p = path.join(REPO_ROOT, ...s.split('.')) + '.lean';
      return fs.existsSync(p) ? p : null;
    }
  }
  return null;
}

/**
 * PHP `contains_module` (lines 518–539): walk leading `import` lines only.
 *
 * @param {string} imp
 * @param {string} target
 * @param {number} depth
 * @param {Set<string>} visited
 */
function importTransitiveContains(imp, target, depth = 0, visited = new Set()) {
  if (depth > TRANSITIVE_IMPORT_MAX_DEPTH) return false;
  if (imp === target) return true;
  if (visited.has(imp)) return false;
  visited.add(imp);
  const abs = resolveImportToLeanPath(imp);
  if (!abs) return false;
  let text;
  try {
    text = fs.readFileSync(abs, 'utf8');
  } catch {
    return false;
  }
  const lines = text.split('\n');
  for (const line of lines) {
    const t = line.trimEnd();
    if (!t.startsWith('import ')) break;
    const child = t.slice('import '.length).trim();
    if (importTransitiveContains(child, target, depth + 1, visited)) return true;
  }
  return false;
}

/**
 * @param {string[]} imports dotted paths (may include `Lemma.` prefix)
 * @returns {string[]} `Tensor.Foo…` modules for `JSON_TABLE` (PHP strips `Lemma.` before encode)
 */
function lemmaRootModulesForMysql(imports) {
  const out = [];
  for (const imp of imports) {
    const s = String(imp);
    if (s.startsWith('Lemma.')) out.push(s.slice('Lemma.'.length));
  }
  return out;
}

/**
 * @param {string[]} rootModulesSansLemma e.g. `['Tensor.SEq.is.SEqDataS.of.Eq']`
 * @param {string} targetImport e.g. `stdlib.SEq`
 * @returns {Promise<number>} match count; 0 on missing pool / empty roots / SQL error
 */
async function countMysqlTransitiveImportHits(rootModulesSansLemma, targetImport) {
  const pool = getMysqlPool();
  if (!pool || !rootModulesSansLemma.length) return 0;
  const json = JSON.stringify(rootModulesSansLemma);
  try {
    const [rows] = await pool.query(MYSQL_TRANSITIVE_IMPORT_SQL, [json, targetImport]);
    const row = rows && rows[0];
    if (!row) return 0;
    const cnt = row.cnt ?? row.CNT ?? Object.values(row)[0];
    return Number(cnt) || 0;
  } catch (e) {
    console.error('[import-syntax-mysql]', e?.message || e);
    return 0;
  }
}

/**
 * Whether `targetImport` is already satisfied by the current `Lemma.*` imports (MySQL deps first,
 * then disk `contains_module` over the same import list).
 *
 * @param {string[]} imports full dotted import list (e.g. `Lemma.Tensor.Foo`, `stdlib.SEq`)
 * @param {string} targetImport e.g. `stdlib.SEq`, `sympy.core.relational`
 */
export async function transitiveProvidesImport(imports, targetImport) {
  const target = String(targetImport).trim();
  const list = imports.map((s) => String(s).trim()).filter(Boolean);
  if (list.includes(target)) return true;

  const roots = lemmaRootModulesForMysql(list);
  const mysqlHits = await countMysqlTransitiveImportHits(roots, target);
  if (mysqlHits > 0) return true;

  for (const imp of list) {
    if (imp.startsWith('Lemma.') && importTransitiveContains(imp, target, 0, new Set())) {
      return true;
    }
  }
  return false;
}

/** Imports that `mergeSyntaxDrivenImports` may add and that PHP may skip when already transitive. */
const PRUNABLE_SYNTAX_IMPORTS = [
  'stdlib.SEq',
  'sympy.core.relational',
  'sympy.core.logic',
  'sympy.core.power',
  'sympy.sets.sets',
  'sympy.concrete.quantifier',
  'sympy.tensor.stack',
  'sympy.tensor.Basic',
  'sympy.polys.domains',
  'sympy.functions.special.tensor_functions',
  'sympy.matrices.expressions.special',
  'sympy.tensor.functions',
];

/**
 * Drop syntax-driven imports that are already implied by `Lemma.*` (MySQL or disk), mirroring PHP
 * `import_syntax` behaviour for POST output.
 *
 * @param {string[]} imports
 * @returns {Promise<string[]>}
 */
export async function pruneRedundantSyntaxImports(imports) {
  let arr = imports.map((s) => String(s).trim()).filter(Boolean);
  for (const t of PRUNABLE_SYNTAX_IMPORTS) {
    if (!arr.includes(t)) continue;
    const rest = arr.filter((x) => x !== t);
    if (await transitiveProvidesImport(rest, t)) {
      arr = rest;
    }
  }
  return arr;
}
