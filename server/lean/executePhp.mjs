/**
 * `php/request/execute.php` — runs `mysql\execute` when MySQL is configured,
 * else stub shapes so the Vue client does not 404.
 */
import { getMysqlConfig, mysqlExecuteLikePhp } from './fetchLemmaMysql.mjs';

function sqlFirstToken(sql) {
  const t = sql.trimStart().match(/^\s*([a-z]+)/i);
  return t ? t[1].toUpperCase() : '';
}

function sendStub(req, res) {
  const sql = (req.body?.sql ?? '').toString();
  if (!sql.trim()) {
    res.type('text/plain').send('0');
    return;
  }

  const head = sqlFirstToken(sql);
  const isRead =
    head === 'SELECT' ||
    head === 'WITH' ||
    head === 'SHOW' ||
    head === 'EXPLAIN' ||
    head === 'DESCRIBE';

  if (isRead) {
    if (/\bcount\s*\(\s*\*\s*\)/i.test(sql)) {
      res.json([{ count: 1 }]);
      return;
    }
    res.json([]);
    return;
  }

  res.type('text/plain').send('1');
}

/**
 * POST body: `sql`, optional `resultType` (PHP MYSQLI_ASSOC=1, MYSQLI_NUM=2).
 * SELECT → JSON array; writes / scalar → plain text (affected rows or `0`).
 */
export async function handleExecutePhp(req, res) {
  if (!getMysqlConfig()) {
    sendStub(req, res);
    return;
  }

  const sql = (req.body?.sql ?? '').toString();
  const resultType = req.body?.resultType;

  if (!sql.trim()) {
    res.type('text/plain').send('0');
    return;
  }

  const out = await mysqlExecuteLikePhp(sql, resultType);
  if (out === null) {
    sendStub(req, res);
    return;
  }
  if (Array.isArray(out)) {
    res.json(out);
    return;
  }
  res.type('text/plain').send(String(out));
}
