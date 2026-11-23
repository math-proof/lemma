#!/usr/bin/env node
import fs from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { compile } from '../js/parser/lean.js';
import { getMysqlPool } from './lean/fetchLemmaMysql.mjs';
import { get_lake_path, get_lean_env, spawnLakeLean } from './lean/echo2vue.mjs';
import { REPO_ROOT, leanPathToModule, moduleToLeanPath } from './lean/modulePath.mjs';
import { fingerprintFormat, fingerprintSignature, parseFingerprint } from './leanInvertedIndex.mjs';
import { structToFingerprint } from './lean/structToFingerprint.mjs';
import { conclusionSearchJson } from './lemmaPath.mjs';

function proofMarker(lines) {
  const main = lines.findIndex(line => /^\s*private lemma main\b/.test(line));
  const markers = lines.flatMap((line, i) => /^\s*-- proof\s*$/.test(line) ? [i] : []);
  const proof = main < 0 && markers.length === 1 ? markers[0] : markers.find(i => main >= 0 && i > main);
  if (proof === undefined) throw Object.assign(new Error('Could not locate the lemma’s -- proof marker'), { probe: true });
  return proof;
}

/** The Lean text of the lemma conclusion: lines after `-- imply`, up to `:=`. */
function conclusionSource(source) {
  const lines = source.replace(/\r\n/g, '\n').split('\n');
  const start = lines.findIndex(line => /^\s*-- imply\s*$/.test(line));
  if (start < 0) return null;
  const out = [];
  for (let i = start + 1; i < lines.length; i++) {
    if (/^\s*--\s*proof\s*$/.test(lines[i])) break;
    const cut = lines[i].indexOf(':=');
    if (cut >= 0) {
      out.push(lines[i].slice(0, cut));
      break;
    }
    out.push(lines[i]);
  }
  return out.join('\n').trim() || null;
}

function instrument(source) {
  const lines = source.replace(/\r\n/g, '\n').split('\n');
  lines.splice(proofMarker(lines) + 1, 0, '  intros');
  const tree = compile(lines.join('\n'));
  tree.relocate_last_comment();
  tree.echo();
  const generated = String(tree).split('\n');
  const proof = proofMarker(generated);
  if (generated[proof + 1]?.trim() !== 'intros' || generated[proof + 2]?.trim() !== 'echo \u22a2') {
    throw Object.assign(new Error('Expected an automatically generated goal Echo after intros'), { probe: true });
  }
  return { source: generated.join('\n'), echoLine: proof + 3 };
}

function readEcho(output, line) {
  for (const text of output.split(/\r?\n/)) {
    const payload = text.replace(/^.*?\.lean:\d+:\d+: info: /, '');
    if (!payload.startsWith('{')) continue;
    let message;
    try {
      message = JSON.parse(payload);
    } catch {
      continue;
    }
    if (typeof message?.[line] === 'string') return message;
  }
  throw Object.assign(new Error('No Echo message found at scratch line ' + line), { probe: true });
}

/** Build the Echo tactic once per process; every probe needs it. */
export async function buildEcho() {
  const cwd = REPO_ROOT;
  const env = { ...get_lean_env(cwd), LEAN_ECHO_SEARCH_JSON: '1' };
  const lake = get_lake_path();
  const build = await spawnLakeLean(lake, ['build', 'Syntax.Tactic.Echo'], { cwd, env });
  if (build.error) throw build.error;
  if (build.status !== 0) throw new Error((build.stdout + build.stderr).trim() || 'Echo build failed');
  return { lake, cwd, env };
}

/**
 * Instrument one lemma, run Lean on it, and return the three views of its
 * conclusion: the stored fingerprint, the JS parse, and the Lean-struct
 * conversion. `pool` and `lean` are optional so a batch can share them.
 */
export async function probeLemma(input, { pool, lean } = {}) {
  const module = input.endsWith('.lean') ? leanPathToModule(input) : input.replace(/^Lemma\./, '');
  if (!module || module.split('.').some(part => !part || /[/\\#]/.test(part))) {
    throw new Error('Invalid lemma module');
  }
  const abs = moduleToLeanPath(module);
  const raw = await fs.readFile(abs, 'utf8');
  const probe = instrument(raw);

  const db = pool ?? getMysqlPool();
  if (!db) throw new Error('MySQL is not configured');
  let stored;
  try {
    const [rows] = await db.execute(
      "SELECT JSON_EXTRACT(meta, '$.fingerprint') AS fingerprint FROM lemma WHERE module = ?",
      [module],
    );
    if (rows.length !== 1) throw new Error('Expected exactly one MySQL lemma row for ' + module);
    stored = parseFingerprint(rows[0].fingerprint);
    if (stored == null) throw new Error('No stored fingerprint for ' + module);
  } finally {
    if (!pool) await db.end();
  }

  const { lake, cwd, env } = lean ?? await buildEcho();
  const tmp = path.join(REPO_ROOT, 'tmp');
  await fs.mkdir(tmp, { recursive: true });
  const dir = await fs.mkdtemp(path.join(tmp, 'lean2json-'));
  try {
    const scratch = path.join(dir, 'Probe.lean');
    await fs.writeFile(scratch, probe.source);
    const result = await spawnLakeLean(lake, ['env', 'lean', scratch], { cwd, env });
    if (result.error) throw result.error;
    if (result.status !== 0) {
      throw Object.assign(new Error((result.stdout + result.stderr).trim() || 'Lean compilation failed'), { probe: true });
    }
    const echo = readEcho(result.stdout + '\n' + result.stderr, probe.echoLine);
    if (echo.struct == null) {
      throw Object.assign(new Error('Echo returned LaTeX only. The structural payload is missing.'), { probe: true });
    }
    const sourceJson = conclusionSearchJson(abs);
    const structJson = structToFingerprint(echo.struct);
    const storedKey = fingerprintSignature(stored);
    return {
      module,
      path: abs,
      echo,
      stored,
      sourceLean: conclusionSource(raw),
      sourceJson,
      structJson,
      sourceMatchesStored: fingerprintSignature(sourceJson) === storedKey,
      structMatchesSource: fingerprintSignature(structJson) === fingerprintSignature(sourceJson),
      structMatchesStored: fingerprintSignature(structJson) === storedKey,
    };
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
}

async function main() {
  const [input, ...extra] = process.argv.slice(2);
  if (!input || input === '--help' || extra.length) {
    console.log('Usage: node mjs/lean2json.mjs <lemma-module-or-lean-file>');
    if (input !== '--help') process.exitCode = 2;
    return;
  }
  const result = await probeLemma(input);
  console.log(JSON.stringify({
    module: result.module,
    path: result.path,
    echo: result.echo,
    sourceMatchesStored: result.sourceMatchesStored,
    structMatchesSource: result.structMatchesSource,
    structMatchesStored: result.structMatchesStored,
    storedFingerprint: fingerprintFormat(result.stored),
    sourceFingerprint: fingerprintFormat(result.sourceJson),
    structFingerprint: fingerprintFormat(result.structJson),
  }, null, 2));
  if (!result.sourceMatchesStored || !result.structMatchesStored) process.exitCode = 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  main().catch(error => {
    console.error(error.message);
    process.exitCode = 1;
  });
}
