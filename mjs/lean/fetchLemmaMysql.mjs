/**
 * Optional MySQL load for lemma pages.
 *
 * Env names match sibling `label/index.js`.
 * When a host is set, the database is `axiom`.
 *
 * Connection is used when `MYSQL_HOST` is set, or when `MYSQL_PWD` is set
 * (host then defaults to `127.0.0.1`, same as `mjs/run.mjs`).
 */
import fs from 'fs';
import path from 'path';
import mysql from 'mysql2/promise';
import { REPO_ROOT, dirExists } from './modulePath.mjs';

/** @type {import('mysql2/promise').Pool | null} */
let pool = null;

/**
 * Canonical `axiom.lemma.module` key: the Lean namespace, with no `Lemma.` / `Theorem.`
 * (or other repo-folder) prefix. `Lemma.Random.X` → `Random.X`. Identity when the
 * module is already the namespace. Used when reading legacy prefixed DB rows;
 * `fetchLemmaRowFromMysql` tries the key, then the raw module string.
 */
export function lemmaModuleKey(module) {
  const m = String(module ?? '').trim();
  const dot = m.indexOf('.');
  if (dot <= 0) return m;
  const head = m.slice(0, dot);
  return dirExists(path.join(REPO_ROOT, head)) ? m.slice(dot + 1) : m;
}

export function leanEchoPath(leanAbsPath) {
  return leanAbsPath.replace(/\.lean$/i, '.echo.lean');
}

/**
 * Load from the database when there is no echo file, or when the
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
/** `MYSQL_HOST`, or `127.0.0.1` when a password is already configured. */
function mysqlHost() {
  const host = (process.env.MYSQL_HOST || '').trim();
  if (host) return host;
  if (process.env.MYSQL_PWD != null && process.env.MYSQL_PWD !== '') return '127.0.0.1';
  return '';
}

export function getMysqlConfig() {
  const host = mysqlHost();
  if (!host) return null;
  const port = Number(process.env.MYSQL_PORT || 3306);
  const database = 'axiom';
  const user = process.env.MYSQL_USER || process.env.USER || process.env.USERNAME;
  const password = process.env.MYSQL_PWD;
  const socketPath = (process.env.MYSQL_SOCKET || '').trim();
  const cfg = probedLogin
    ? { host, port, database, ...probedLogin }
    : { host, port, user, password, database };
  // mysql2 prefers `host` and opens TCP. `root@localhost` on the server is the
  // socket account, so a socket must replace the host.
  if (socketPath) {
    cfg.socketPath = socketPath;
    delete cfg.host;
  }
  return cfg;
}

/**
 * The OS user name is not always a MySQL account (e.g. WSL user `cosmos`, while the DB has
 * `prod` / `Administrator`), which made every query fail with "Access denied" and the lemma
 * page fall back to re-rendering from source. Same candidates as `mjs/run.mjs`.
 * @type {{ user: string, password: string } | null}
 */
let probedLogin = null;

async function probeMysqlLogin() {
  const host = mysqlHost();
  if (!host) return;
  const port = Number(process.env.MYSQL_PORT || 3306);
  const pwd = process.env.MYSQL_PWD;
  const candidates = [];
  if (process.env.MYSQL_USER) candidates.push({ user: process.env.MYSQL_USER, password: pwd });
  const osUser = process.env.USER || process.env.USERNAME;
  if (osUser) candidates.push({ user: osUser, password: pwd });
  candidates.push({ user: 'prod', password: pwd }, { user: 'prod', password: 'prod' });
  candidates.push({ user: 'user', password: 'user' });
  for (const c of candidates) {
    if (c.password == null) continue;
    try {
      const socketPath = (process.env.MYSQL_SOCKET || '').trim();
      const conn = await mysql.createConnection({
        ...(socketPath ? { socketPath } : { host, port }),
        database: 'axiom', user: c.user, password: c.password, connectTimeout: 3000,
      });
      await conn.end();
      probedLogin = c;
      return;
    } catch {
      /* try next */
    }
  }
}

await probeMysqlLogin();

export function getMysqlPool() {
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
    /** Allow several statements separated by `;`. */
    multipleStatements: true,
  });
  return pool;
}

/** Result shapes: assoc, numeric, or both. */
const MYSQLI_ASSOC = 1;
const MYSQLI_NUM = 2;
const MYSQLI_BOTH = 3;

function parseMysqliResultType(v) {
  const n = Number(v);
  if (Number.isFinite(n)) return n;
  return MYSQLI_NUM;
}

/**
 * Run one SQL statement for `request/execute`.
 * @param {string} sql
 * @param {unknown} resultType POST `resultType` (`MYSQLI_NUM` = 2)
 * @returns {Promise<unknown[] | number | null>} `null` if MySQL not configured
 */
export async function mysqlExecute(sql, resultType) {
  const p = getMysqlPool();
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
    const header = rows;
    return header.affectedRows ?? 0;
  } catch (e) {
    console.warn('[mysql execute]', e.message);
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

/** Empty arrays count as missing lemma or date values. */
function isEmptyDecodedLemmaField(v) {
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
  code.preamble = decode(code.preamble);
  code.lemma = decode(code.lemma);
  let meta = decode(code.meta);
  if (meta == null || typeof meta !== 'object' || Array.isArray(meta))
    meta = {};
  if (!Array.isArray(meta.error))
    meta.error = [];
  code.meta = meta;
  code.date = decode(code.date);
  code.module = lemmaModuleKey(module);
  code.user = user;
  if (isEmptyDecodedLemmaField(code.lemma) || isEmptyDecodedLemmaField(code.date)) return null;
  return code;
}

/**
 * @param {string} module
 * @returns {Promise<Record<string, unknown> | null>}
 */
export async function fetchLemmaRowFromMysql(module) {
  const p = getMysqlPool();
  if (!p) return null;
  const key = lemmaModuleKey(module);
  const keys = [key];
  if (module && module !== key) keys.push(module);
  // Legacy rows may still be stored as `Lemma.Random.X` / `Theorem.Random.X`.
  for (const folder of ['Lemma', 'Theorem']) {
    const legacy = `${folder}.${key}`;
    if (key && !keys.includes(legacy)) keys.push(legacy);
  }
  for (const k of keys) {
    const [rows] = await p.query(
      'SELECT * FROM lemma WHERE module = ? ORDER BY id DESC LIMIT 1',
      [k]
    );
    if (Array.isArray(rows) && rows.length > 0) {
      const row = /** @type {Record<string, unknown>} */ (rows[0]);
      await applyDocstringComments(p, row);
      return row;
    }
  }
  return null;
}

/**
 * Drop each declaration's `comment` so it is stored in `axiom.docstring`, not in `lemma` JSON.
 * Empty comments are dropped and not inserted.
 * @param {unknown} lemmas
 * @returns {{ lemmas: unknown[], rows: [number, string][] }}
 */
export function peelDocstrings(lemmas) {
  const list = Array.isArray(lemmas) ? lemmas : [];
  /** @type {[number, string][]} */
  const rows = [];
  const stored = list.map((lemma, lemmaId) => {
    if (!lemma || typeof lemma !== 'object' || Array.isArray(lemma)) return lemma;
    const src = /** @type {Record<string, unknown>} */ (lemma);
    if (!Object.prototype.hasOwnProperty.call(src, 'comment')) return lemma;
    const text = typeof src.comment === 'string' ? src.comment : '';
    if (text.trim()) rows.push([lemmaId, text]);
    const copy = { ...src };
    delete copy.comment;
    return copy;
  });
  return { lemmas: stored, rows };
}

/**
 * Put `docstring.text` back on `lemma[lemma_id].comment` for the Vue payload.
 * @param {import('mysql2/promise').Pool | import('mysql2/promise').PoolConnection | import('mysql2/promise').Connection} conn
 * @param {Record<string, unknown>} row
 */
async function applyDocstringComments(conn, row) {
  const id = Number(row.id);
  if (!Number.isFinite(id)) return;
  const [docs] = await conn.query(
    'SELECT lemma_id, text FROM docstring WHERE id = ?',
    [id]
  );
  if (!Array.isArray(docs) || docs.length === 0) return;
  const lemmas = decode(row.lemma);
  if (!Array.isArray(lemmas)) return;
  for (const doc of docs) {
    const i = Number(doc.lemma_id);
    const lemma = lemmas[i];
    if (lemma && typeof lemma === 'object' && !Array.isArray(lemma))
      lemma.comment = doc.text;
  }
  row.lemma = lemmas;
}

/**
 * Replace every docstring row for one lemma file.
 * @param {import('mysql2/promise').PoolConnection | import('mysql2/promise').Connection} conn
 * @param {number} id axiom.lemma.id
 * @param {[number, string][]} rows
 */
export async function replaceDocstrings(conn, id, rows) {
  await conn.query('DELETE FROM docstring WHERE id = ?', [id]);
  if (!rows.length) return;
  await conn.query(
    'INSERT INTO docstring (id, lemma_id, text) VALUES ?',
    [rows.map(([lemmaId, text]) => [id, lemmaId, text])]
  );
}

/**
 * One `mathlib` row by exact `name`.
 * @param {string} name
 * @returns {Promise<Record<string, unknown> | null>}
 */
export async function fetchMathlibRowByName(name) {
  const p = getMysqlPool();
  if (!p) return null;
  const nm = name == null ? '' : String(name).trim();
  if (!nm) return null;
  try {
    const [rows] = await p.query('SELECT * FROM `mathlib` WHERE `name` = ? LIMIT 1', [nm]);
    if (!Array.isArray(rows) || rows.length === 0) return null;
    return /** @type {Record<string, unknown>} */ (rows[0]);
  } catch (e) {
    console.warn('[mathlib row by name]', e.message);
    return null;
  }
}

/**
 * Map one `mathlib` table row to the `lemma` prop shape expected by `mathlib.vue` / `lemma.vue`.
 * Column order follows `sql/create/mathlib.sql`.
 * @param {Record<string, unknown>} row
 */
export function mathlibRowToLemmaPayload(row) {
  const r = row;
  const implyRaw = decode(r.imply);
  /** Decode `imply` as stored. The database value is kept. */
  const imply =
    implyRaw != null && typeof implyRaw === 'object'
      ? /** @type {Record<string, unknown>} */ ({ ...implyRaw })
      : { insert: true, lean: '', latex: '' };
  const givenDec = decode(r.given);
  let given = Array.isArray(givenDec) ? givenDec : givenDec != null ? [givenDec] : null;
  if (isEmptyDecodedLemmaField(given)) given = null;
  return {
    name: String(r.name ?? ''),
    type: r.type != null ? String(r.type) : '',
    instImplicit: r.instImplicit != null ? String(r.instImplicit) : '',
    strictImplicit: r.strictImplicit != null ? String(r.strictImplicit) : '',
    implicit: r.implicit != null ? String(r.implicit) : '',
    explicit: r.explicit != null ? String(r.explicit) : '',
    given,
    default: r.default != null ? String(r.default) : '',
    imply,
    proof: {},
  };
}

/**
 * @param {string} name dotted Mathlib name (may be empty)
 * @param {number} [limit]
 * @returns {Promise<object[]>} payloads for `createApp('mathlib', { lemma })`
 */
export async function fetchMathlibLemmaPayloadsFromMysql(name, limit = 100) {
  const p = getMysqlPool();
  if (!p) return [];
  const lim = Math.min(Math.max(Number(limit) || 100, 1), 500);
  const nm = name == null ? '' : String(name).trim();
  try {
    if (nm) {
      const [exact] = await p.query('SELECT * FROM mathlib WHERE `name` = ? LIMIT ?', [nm, lim]);
      if (Array.isArray(exact) && exact.length > 0) {
        return exact.map((row) => mathlibRowToLemmaPayload(row));
      }
      const esc = nm.replace(/(?<!\\)\\b/g, '\\\\b');
      const [rx] = await p.query(
        'SELECT * FROM mathlib WHERE `name` COLLATE utf8mb4_bin REGEXP ? LIMIT ?',
        [esc, lim]
      );
      if (Array.isArray(rx) && rx.length > 0) {
        return rx.map((row) => mathlibRowToLemmaPayload(row));
      }
      return [];
    }
    const [rand] = await p.query(
      'SELECT * FROM mathlib WHERE json_length(`imply`) = 0 ORDER BY RAND() LIMIT ?',
      [lim]
    );
    return Array.isArray(rand)
      ? rand.map((row) => mathlibRowToLemmaPayload(row))
      : [];
  } catch (e) {
    console.warn('[mathlib mysql]', e.message);
    return [];
  }
}

/**
 * @param {string} echoAbsPath
 */
export function ensureEmptyEchoFile(echoAbsPath) {
  if (fs.existsSync(echoAbsPath)) return;
  fs.mkdirSync(path.dirname(echoAbsPath), { recursive: true });
  fs.writeFileSync(echoAbsPath, '', 'utf8');
}
