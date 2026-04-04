/**
 * Optional MySQL load for lemma pages — mirrors php/lemma.php (lines 500–515)
 * and php/utility.php `fetch_from_mysql`.
 *
 * Env names match sibling `label/index.js`:
 *   MYSQL_HOST, MYSQL_USER, MYSQL_PWD, MYSQL_DATABASE, MYSQL_PORT
 *
 * Defaults when a host is set match php/init.php (DB `axiom`, user/user),
 * not label’s default DB (`corpus`).
 *
 * Connection is used only if MYSQL_HOST is non-empty.
 */
import fs from 'fs';
import path from 'path';
import mysql from 'mysql2/promise';

/** @type {import('mysql2/promise').Pool | null} */
let pool = null;

export function leanEchoPath(leanAbsPath) {
  return leanAbsPath.replace(/\.lean$/i, '.echo.lean');
}

/**
 * Same condition as PHP: load from DB when there is no echo file, or when the
 * echo sidecar is newer than the `.lean` file (lean on disk is stale).
 */
export function shouldLoadLemmaFromMysql(leanAbsPath, echoAbsPath) {
  if (!fs.existsSync(echoAbsPath)) return true;
  try {
    const leanStat = fs.statSync(leanAbsPath);
    const echoStat = fs.statSync(echoAbsPath);
    return leanStat.mtimeMs < echoStat.mtimeMs;
  } catch {
    return true;
  }
}

/**
 * Same shape as `../label/index.js` pool options.
 * @returns {{ host: string, port: number, user: string, password: string, database: string } | null}
 */
export function getMysqlConfig() {
  const host = (process.env.MYSQL_HOST || '').trim();
  if (!host) return null;
  const port = Number(process.env.MYSQL_PORT || 3306);
  const user = process.env.MYSQL_USER || 'user';
  const password = process.env.MYSQL_PWD ?? process.env.MYSQL_PASSWORD ?? 'user';
  const database = 'axiom';
  return { host, port, user, password, database };
}

function getPool() {
  if (pool) return pool;
  const cfg = getMysqlConfig();
  if (!cfg) return null;
  pool = mysql.createPool({
    ...cfg,
    waitForConnections: true,
    connectionLimit: 8,
    queueLimit: 0,
    enableKeepAlive: true,
    keepAliveInitialDelay: 0,
    /** Match PHP `mysql\execute` multi-statement (`implode(';', $sql)`). */
    multipleStatements: true,
  });
  return pool;
}

/** PHP `MYSQLI_ASSOC` / `MYSQLI_NUM` / `MYSQLI_BOTH` */
const MYSQLI_ASSOC = 1;
const MYSQLI_NUM = 2;
const MYSQLI_BOTH = 3;

function parseMysqliResultType(v) {
  const n = Number(v);
  if (Number.isFinite(n)) return n;
  return MYSQLI_NUM;
}

/**
 * Port of `mysql\execute` (php/mysql.php) for `php/request/execute.php`.
 * @param {string} sql
 * @param {unknown} resultType POST `resultType` (PHP default `MYSQLI_NUM` = 2)
 * @returns {Promise<unknown[] | number | null>} `null` if MySQL not configured
 */
export async function mysqlExecuteLikePhp(sql, resultType) {
  const p = getPool();
  if (!p) return null;
  try {
    const [rows, fields] = await p.query(sql);
    if (Array.isArray(rows)) {
      const rt = parseMysqliResultType(resultType);
      if (rt === MYSQLI_ASSOC) return rows;
      if (rt === MYSQLI_NUM) {
        if (!fields?.length) return [];
        const names = fields.map((f) => f.name);
        return rows.map((row) => names.map((name) => row[name]));
      }
      if (rt === MYSQLI_BOTH) {
        if (!fields?.length) return [];
        const names = fields.map((f) => f.name);
        return rows.map((row) => {
          const o = { ...row };
          names.forEach((name, i) => {
            o[i] = row[name];
          });
          return o;
        });
      }
      return rows;
    }
    const header = /** @type {import('mysql2').ResultSetHeader} */ (rows);
    return header.affectedRows ?? 0;
  } catch (e) {
    console.warn('[mysql execute]', /** @type {Error} */ (e).message);
    return 0;
  }
}

/**
 * @param {string} jsonOrNull
 * @returns {unknown}
 */
function decode(jsonOrNull) {
  if (jsonOrNull == null || jsonOrNull === '') return null;
  if (typeof jsonOrNull !== 'string') return jsonOrNull;
  try {
    return JSON.parse(jsonOrNull);
  } catch {
    return null;
  }
}

/** PHP-like falsy for decoded lemma / date (PHP treats [] as empty). */
function isEmptyForPhp(v) {
  if (v == null) return true;
  if (Array.isArray(v)) return v.length === 0;
  if (typeof v === 'string') return v.length === 0;
  if (typeof v === 'object') return Object.keys(v).length === 0;
  return false;
}

/**
 * @param {Record<string, unknown>} row
 * @param {string} module
 * @param {string} user
 * @returns {object | null} Vue payload, or null if row is unusable
 */
export function codeFromMysqlRow(row, module, user) {
  if (!row) return null;
  const code = { ...row };
  code.imports = decode(code.imports);
  code.open = decode(code.open);
  code.def = decode(code.def);
  code.lemma = decode(code.lemma);
  code.error = decode(code.error);
  code.date = decode(code.date);
  code.module = module;
  code.user = user;
  if (isEmptyForPhp(code.lemma) || isEmptyForPhp(code.date)) return null;
  return code;
}

/**
 * @param {string} user
 * @param {string} module
 * @returns {Promise<Record<string, unknown> | null>}
 */
export async function fetchLemmaRowFromMysql(user, module) {
  const p = getPool();
  if (!p) return null;
  const [rows] = await p.query(
    'SELECT * FROM lemma WHERE user = ? AND module = ? LIMIT 1',
    [user, module]
  );
  if (!Array.isArray(rows) || rows.length === 0) return null;
  return /** @type {Record<string, unknown>} */ (rows[0]);
}

/**
 * @param {string} echoAbsPath
 */
export function ensureEmptyEchoFile(echoAbsPath) {
  if (fs.existsSync(echoAbsPath)) return;
  fs.mkdirSync(path.dirname(echoAbsPath), { recursive: true });
  fs.writeFileSync(echoAbsPath, '', 'utf8');
}
