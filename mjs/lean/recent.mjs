/**
 * GET `request/recent` — recent modules by file mtime.
 */
import fs from 'fs';
import path from 'path';
import { REPO_ROOT, leanPathToModule } from './modulePath.mjs';

/**
 * @param {import('express').Request} req
 * @param {import('express').Response} res
 */
export function handleRecent(req, res) {
  const topk = Math.min(100, Math.max(1, Number(req.query.top) || 10));
  const lemmaRoot = path.join(REPO_ROOT, 'Lemma');
  /** @type {{ mtimeMs: number, mod: string }[]} */
  const items = [];

  /**
   * `sh/run.sh` writes import-batch scratch files at Lemma/test.lean,
   * Lemma/test.N.lean, and Lemma/test.<section>*.lean (gitignored as test.*).
   * They are not axioms and must not appear in the recent list.
   * Real lemmas such as Nat.TestBit / Set.TestFunctionActionHom stay included.
   */
  function isRunShTestModule(mod) {
    return mod === 'test' || mod.startsWith('test.');
  }

  function walk(dir) {
    let entries;
    try {
      entries = fs.readdirSync(dir, { withFileTypes: true });
    } catch {
      return;
    }
    for (const ent of entries) {
      const p = path.join(dir, ent.name);
      if (ent.isDirectory()) {
        walk(p);
      } else if (
        ent.isFile() &&
        ent.name.endsWith('.lean') &&
        !ent.name.endsWith('.echo.lean')
      ) {
        const mod = leanPathToModule(p);
        if (!mod || isRunShTestModule(mod)) continue;
        try {
          const st = fs.statSync(p);
          items.push({ mtimeMs: st.mtimeMs, mod });
        } catch {
          /* skip */
        }
      }
    }
  }

  walk(lemmaRoot);
  items.sort((a, b) => b.mtimeMs - a.mtimeMs);
  res.type('application/json').json(items.slice(0, topk).map((x) => x.mod));
}
