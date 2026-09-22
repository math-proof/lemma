/**
 * fetchLemmaJson.mjs — Name.toJson for a Lemma/*.lean via path-derived private main
 */
import fs from 'fs';
import path from 'path';
import { spawnSync } from 'child_process';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, '..');

/** Lemma/List/Foo/eq/Bar.lean → _private.Lemma.List.Foo.eq.Bar.0.main */
export function privateMainFromLemmaPath(leanRelPath) {
  let p = leanRelPath.replace(/\\/g, '/');
  if (p.startsWith('Lemma/')) p = p.slice('Lemma/'.length);
  p = p.replace(/\.lean$/, '');
  const parts = p.split('/').filter(Boolean);
  return {
    moduleParts: parts,
    privateNameLean:
      'Name.mkStr (Name.mkNum `_private.Lemma.' + parts.join('.') + ' 0) "main"',
    display:
      '_private.Lemma.' + parts.join('.') + '.0.main',
  };
}

export function fetchLemmaJson(leanFileAbs, { timeoutMs = 120000 } = {}) {
  const rel = path.relative(REPO, leanFileAbs).replace(/\\/g, '/');
  if (!rel.startsWith('Lemma/')) {
    throw new Error('expected path under Lemma/: ' + rel);
  }
  const { privateNameLean, display, moduleParts } = privateMainFromLemmaPath(rel);
  const moduleName = 'Lemma.' + moduleParts.join('.');
  const probe = path.join(REPO, '_suggest_probe.lean');
  const src =
    'import ' + moduleName + '\n' +
    'import sympy.printing.json\n' +
    'open Lean Meta\n\n' +
    '#eval show MetaM Unit from do\n' +
    '  let n := ' + privateNameLean + '\n' +
    '  let j ← Name.toJson n\n' +
    '  IO.println (Json.compress j)\n';
  fs.writeFileSync(probe, src, 'utf8');
  const lake = process.env.LEAN_LAKE_PATH || 'lake';
  const r = spawnSync(lake, ['env', 'lean', probe], {
    cwd: REPO,
    encoding: 'utf8',
    timeout: timeoutMs,
    maxBuffer: 64 * 1024 * 1024,
  });
  try { fs.unlinkSync(probe); } catch {}
  if (r.error) throw r.error;
  const out = (r.stdout || '') + (r.stderr || '');
  const lines = out.split(/\r?\n/).filter((l) => l.startsWith('{'));
  if (!lines.length) {
    throw new Error('Name.toJson produced no JSON for ' + display + '\n' + out.slice(-2000));
  }
  return { name: display, json: JSON.parse(lines[lines.length - 1]), moduleName };
}

/** `_private.Lemma.Set.Foo.0.main` → `Lemma.Set.Foo` */
function moduleFromDecl(decl) {
  const m = /^_private\.(.*)\.0\.main$/.exec(String(decl));
  return m ? m[1] : null;
}

function repoRel(abs) {
  return path.relative(REPO, abs).replace(/\\/g, '/');
}

/** `Lemma/Set/Foo.lean` → `Lemma.Set.Foo` */
function moduleOf(rel) {
  return rel.replace(/\.lean$/, '').split('/').filter(Boolean).join('.');
}

/**
 * Does Lean have a current `.olean` for this file? A missing or stale one means the
 * probe would fail (or silently check an outdated type), so it is reported instead.
 */
function oleanState(rel) {
  const olean = path.join(REPO, '.lake', 'build', 'lib', 'lean', rel.replace(/\.lean$/, '.olean'));
  try {
    if (!fs.existsSync(olean)) return 'not built (no .olean)';
    if (fs.statSync(olean).mtimeMs < fs.statSync(path.join(REPO, rel)).mtimeMs) {
      return 'stale .olean (run lake build)';
    }
    return '';
  } catch (e) {
    return 'cannot stat .olean';
  }
}

/** One `lake env lean` process for a whole chunk of modules. @returns Map(module → {json|error}) */
function probeChunk(chunkRel, timeoutMs) {
  const mods = chunkRel.map(moduleOf);
  const names = mods.map((m) => `    Name.mkStr (Name.mkNum \`_private.${m} 0) "main"`);
  const probe = path.join(REPO, '_scan_probe.lean');
  const src =
    mods.map((m) => 'import ' + m).join('\n') +
    '\nimport sympy.printing.json\n' +
    'open Lean Meta\n\n' +
    '#eval show MetaM Unit from do\n' +
    '  let ns : List Name := [\n' +
    names.join(',\n') +
    '\n  ]\n' +
    '  for n in ns do\n' +
    '    try\n' +
    '      let j ← Name.toJson n\n' +
    '      IO.println (Json.compress (Json.mkObj [("decl", toJson (toString n)), ("json", j)]))\n' +
    '    catch _ =>\n' +
    '      IO.println (Json.compress (Json.mkObj [("decl", toJson (toString n)), ("error", toJson "Name.toJson failed")]))\n';
  fs.writeFileSync(probe, src, 'utf8');
  try {
    const lake = process.env.LEAN_LAKE_PATH || 'lake';
    const r = spawnSync(lake, ['env', 'lean', probe], {
      cwd: REPO,
      encoding: 'utf8',
      timeout: timeoutMs,
      maxBuffer: 256 * 1024 * 1024,
    });
    const out = (r.stdout || '') + (r.stderr || '');
    const got = new Map();
    for (const line of out.split(/\r?\n/)) {
      if (!line.startsWith('{')) continue;
      let o;
      try {
        o = JSON.parse(line);
      } catch {
        continue;
      }
      const mod = moduleFromDecl(o.decl);
      if (mod) got.set(mod, o.json ? { json: o.json } : { error: String(o.error || 'error') });
    }
    if (!got.size) {
      throw new Error('probe produced no JSON (chunk of ' + chunkRel.length + ')\n' + out.slice(-2000));
    }
    return got;
  } finally {
    try {
      fs.unlinkSync(probe);
    } catch {}
  }
}

/**
 * Batch `fetchLemmaJson`: one Lean process per chunk. Measured ≈8.8 s per process no
 * matter how few modules it holds (the fixed lake/lean startup dominates), so chunking is
 * what makes a whole-tree scan affordable — 4495 modules ≈ 23 chunks ≈ 4 min instead of
 * ~18 h at one process per file. A failing chunk is bisected down to the culprit module.
 *
 * @param {string[]} lemmaAbsPaths
 * @param {{chunkSize?: number, timeoutMs?: number, onChunk?: (done: number, total: number) => void, onResults?: (soFar: (object | undefined)[], done: number, total: number) => void}} [opts]
 *   `onResults` fires after each chunk with the input-aligned results so far
 *   (still-`undefined` slots = not probed yet) — lets callers persist partials.
 * @returns {Array<{file: string, json?: object, error?: string}>} input order, `file` repo-relative
 */
export function fetchLemmaJsonBatch(lemmaAbsPaths, { chunkSize = 200, timeoutMs = 900000, onChunk, onResults } = {}) {
  const results = new Map();
  const pending = [];
  for (const abs of lemmaAbsPaths) {
    const rel = repoRel(abs);
    if (!rel.startsWith('Lemma/')) {
      results.set(abs, { file: rel, error: 'not under Lemma/' });
      continue;
    }
    const bad = oleanState(rel);
    if (bad) results.set(abs, { file: rel, error: bad });
    else pending.push(abs);
  }

  const collect = (chunk) => {
    if (!chunk.length) return;
    const rels = chunk.map(repoRel);
    let got;
    try {
      got = probeChunk(rels, timeoutMs);
    } catch (e) {
      if (chunk.length === 1) {
        results.set(chunk[0], { file: rels[0], error: String(e?.message || e).split('\n')[0] });
        return;
      }
      const mid = Math.ceil(chunk.length / 2);
      collect(chunk.slice(0, mid));
      collect(chunk.slice(mid));
      return;
    }
    chunk.forEach((abs, i) => {
      const hit = got.get(moduleOf(rels[i]));
      if (!hit) results.set(abs, { file: rels[i], error: 'no JSON line from probe' });
      else if (hit.error) results.set(abs, { file: rels[i], error: hit.error });
      else results.set(abs, { file: rels[i], json: hit.json });
    });
  };

  for (let i = 0; i < pending.length; i += chunkSize) {
    collect(pending.slice(i, i + chunkSize));
    onChunk?.(Math.min(i + chunkSize, pending.length), pending.length);
    onResults?.(
      lemmaAbsPaths.map((abs) => results.get(abs)),
      Math.min(i + chunkSize, pending.length),
      pending.length,
    );
  }
  return lemmaAbsPaths.map((abs) => results.get(abs));
}
