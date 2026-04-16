/**
 * Node implementation of `php/request/mathlib.php`: run a one-off Lean file that
 * `println!`s `Name.toJson` for a Mathlib name, return the JSON object (same contract
 * the browser expects from `form_post` + destructuring in `mathlib.vue`).
 */
import path from 'path';
import fs from 'fs/promises';
import { REPO_ROOT } from './modulePath.mjs';
import { get_lake_path, get_lean_env, spawnLakeLean } from './echo2vue.mjs';

/**
 * @param {string} text
 * @returns {Record<string, unknown> | null}
 */
function extractJsonObjectFromLeanOutput(text) {
  if (!text || typeof text !== 'string') return null;
  const tryParse = (t) => {
    try {
      const v = JSON.parse(t);
      return v != null && typeof v === 'object' && !Array.isArray(v) ? /** @type {Record<string, unknown>} */ (v) : null;
    } catch {
      return null;
    }
  };
  const trimmed = text.trim();
  let o = tryParse(trimmed);
  if (o) return o;
  const lines = text.split('\n');
  for (let i = lines.length - 1; i >= 0; i--) {
    const chunk = lines.slice(i).join('\n').trim();
    o = tryParse(chunk);
    if (o && ('name' in o || 'type' in o)) return o;
  }
  const start = text.indexOf('{');
  if (start < 0) return null;
  let depth = 0;
  for (let i = start; i < text.length; i++) {
    const c = text[i];
    if (c === '{') depth++;
    else if (c === '}') {
      depth--;
      if (depth === 0) {
        o = tryParse(text.slice(start, i + 1));
        if (o) return o;
      }
    }
  }
  return null;
}

/**
 * POST body: `name` (urlencoded) — dotted Mathlib constant name.
 * @param {import('express').Request} req
 * @param {import('express').Response} res
 */
export async function handleMathlibPhpRequest(req, res) {
  const nameRaw = req.body?.name;
  if (nameRaw == null || String(nameRaw).trim() === '') {
    res.status(400).json({ error: 'missing name' });
    return;
  }
  const name = String(nameRaw).trim();
  const relFile = `test.${name.replace(/\?/g, '%3F')}.lean`;
  const absFile = path.join(REPO_ROOT, relFile);
  const codeStr = `import Mathlib
import sympy.printing.json
#eval do
  println! ← Name.toJson \`${name}
`;

  await fs.writeFile(absFile, codeStr, 'utf8');
  try {
    const lakePath = get_lake_path();
    const env = get_lean_env(REPO_ROOT);
    const r = await spawnLakeLean(lakePath, ['env', 'lean', absFile], {
      cwd: REPO_ROOT,
      env,
      windowsHide: true,
    });
    if (r.error) {
      res.status(502).json({
        error: 'lean spawn failed',
        detail: r.error.message,
        stderr: (r.stderr || '').slice(0, 4000),
        stdout: (r.stdout || '').slice(0, 4000),
      });
      return;
    }
    const outText = `${r.stdout || ''}\n${r.stderr || ''}`;
    const json = extractJsonObjectFromLeanOutput(outText);
    if (!json) {
      res.status(502).json({
        error: 'no JSON object in Lean output',
        raw: outText.slice(0, 8000),
      });
      return;
    }
    res.type('application/json; charset=utf-8').json(json);
  } catch (e) {
    console.error('[mathlib.php]', e);
    res.status(500).json({ error: String(/** @type {Error} */ (e).message || e) });
  } finally {
    try {
      await fs.unlink(absFile);
    } catch {
      /* ignore */
    }
  }
}
