/**
 * Stand-in for `php/request/execute.php` when MySQL is not available.
 * PHP runs real SQL; here we only return shapes the Vue client tolerates:
 * - SELECT → JSON array (empty, or one row for `count(*)` so `window.close` hash does not spin forever)
 * - writes → plain affected-row count like PHP `echo` for non-array results
 */

function sqlFirstToken(sql) {
  const t = sql.trimStart().match(/^\s*([a-z]+)/i);
  return t ? t[1].toUpperCase() : '';
}

export function handleExecutePhpStub(req, res) {
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
