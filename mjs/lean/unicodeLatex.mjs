/**
 * Exact latex-alias lookup for the one-line search box.
 * CodeMirror reads the same `unicode.latex` JSON; here a trailing space commits
 * `\^2` to `²` without mounting the editor.
 */
import { getMysqlPool } from './fetchLemmaMysql.mjs';

export async function handleUnicodeLatex(req, res) {
  const latex = String(req.query.latex ?? '');
  if (!latex || latex.length > 64 || /[\0\r\n]/.test(latex)) {
    res.json({ unicode: null });
    return;
  }

  const pool = getMysqlPool();
  if (!pool) {
    res.json({ unicode: null });
    return;
  }

  const [rows] = await pool.query(
    `SELECT DISTINCT u.unicode AS unicode
     FROM unicode u
     CROSS JOIN JSON_TABLE(u.latex, '$[*]' COLUMNS (latex varchar(255) PATH '$')) jt
     WHERE u.latex IS NOT NULL AND jt.latex = BINARY ?
     LIMIT 2`,
    [latex],
  );

  res.json({ unicode: rows.length === 1 ? rows[0].unicode : null });
}
