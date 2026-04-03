/**
 * Port of `LeanModule::echo2vue` (php/parser/lean.php ~4738–4852).
 * Runs from repo root via subprocess `cwd` (no `process.chdir`).
 */
import fs from 'fs';
import path from 'path';
import { execSync, spawnSync } from 'child_process';
import { REPO_ROOT } from './modulePath.mjs';
import { leanEchoPath } from './fetchLemmaMysql.mjs';
import { LeanModule, LeanTactic } from '../../static/js/parser/lean.js';

/** @param {unknown} stmt */
function isLeanImport(stmt) {
  return (
    stmt != null &&
    typeof stmt === 'object' &&
    /** @type {{ constructor?: { name?: string } }} */ (stmt).constructor?.name === 'Lean_import'
  );
}

/** @param {unknown} stmt */
function importPackageString(stmt) {
  return String(/** @type {{ arg: unknown }} */ (stmt).arg).trim();
}

function getLakePath() {
  if (process.env.LEAN_LAKE_PATH) return process.env.LEAN_LAKE_PATH;
  const home = process.env.USERPROFILE || process.env.HOME || '';
  const exe = process.platform === 'win32' ? 'lake.exe' : 'lake';
  return path.join(home, '.elan', 'bin', exe);
}

/** @param {string} repoRoot */
function buildLeanEnv(repoRoot) {
  const pkgsDir = path.join(repoRoot, '.lake', 'packages');
  let repos = [];
  try {
    repos = fs.readdirSync(pkgsDir).filter((x) => x !== '.' && x !== '..');
  } catch {
    /* no .lake/packages */
  }
  const cwdUnix = repoRoot.replace(/\\/g, '/');
  const env = { ...process.env };
  env.GIT_CONFIG_COUNT = String(repos.length);
  repos.forEach((directory, index) => {
    env[`GIT_CONFIG_KEY_${index}`] = 'safe.directory';
    env[`GIT_CONFIG_VALUE_${index}`] = `${cwdUnix}/.lake/packages/${directory}`;
  });
  return env;
}

/**
 * @param {InstanceType<typeof LeanModule>} tree
 * @param {string} repoRoot
 */
function collectStaleLemmaImports(tree, repoRoot) {
  /** @type {unknown[]} */
  const out = [];
  for (const stmt of tree.args) {
    if (!isLeanImport(stmt)) continue;
    const pkg = importPackageString(stmt);
    if (!pkg.startsWith('Lemma.')) continue;
    const moduleSlash = pkg.replace(/\./g, '/');
    const olean = path.join(repoRoot, '.lake', 'build', 'lib', 'lean', `${moduleSlash}.olean`);
    const leanFs = path.join(repoRoot, `${moduleSlash}.lean`);
    let stale = false;
    try {
      if (!fs.existsSync(olean)) stale = true;
      else if (fs.existsSync(leanFs) && fs.statSync(olean).mtimeMs < fs.statSync(leanFs).mtimeMs) {
        stale = true;
      }
    } catch {
      stale = true;
    }
    if (stale) out.push(stmt);
  }
  return out;
}

/** Lean diagnostic line: `path.lean:line:col: severity: message` */
const DIAG_RE = /^(.+\.lean):(\d+):(\d+): (\w+): (.+)$/;

/**
 * @param {InstanceType<typeof LeanModule>} tree
 * @param {string} leanFileAbs absolute path to the source `.lean` file
 * @param {{ module?: string }} [opts]
 */
export function runEcho2Vue(tree, leanFileAbs, opts = {}) {
  if (!(tree instanceof LeanModule)) throw new Error('runEcho2Vue expects LeanModule');
  const repoRoot = REPO_ROOT;
  const leanEchoFile = leanEchoPath(path.resolve(leanFileAbs));

  tree.relocate_last_comment();
  tree.echo();

  if (!fs.existsSync(leanEchoFile)) {
    fs.mkdirSync(path.dirname(leanEchoFile), { recursive: true });
    fs.writeFileSync(leanEchoFile, '', 'utf8');
  }
  const codeStr = String(tree);
  fs.writeFileSync(leanEchoFile, codeStr, 'utf8');

  const lakePath = getLakePath();
  const env = buildLeanEnv(repoRoot);
  const staleImports = collectStaleLemmaImports(tree, repoRoot);
  if (staleImports.length) {
    const names = staleImports.map((s) => importPackageString(s));
    const quoted = names.map((n) => `"${n.replace(/"/g, '\\"')}"`).join(' ');
    const cmd = `"${lakePath}" build ${quoted}`;
    try {
      execSync(cmd, { cwd: repoRoot, env, stdio: 'pipe', shell: true });
    } catch (e) {
      console.warn('[echo2vue] lake build:', /** @type {Error} */ (e).message || e);
    }
  }

  const echoArg = path.resolve(leanEchoFile);
  const leanArgs = [
    'env',
    'lean',
    '-Dlinter.unusedTactic=false',
    '-Dlinter.dupNamespace=false',
    '-Ddiagnostics.threshold=1000',
    '-DmaxHeartbeats=4000000',
    echoArg,
  ];
  const r = spawnSync(lakePath, leanArgs, {
    cwd: repoRoot,
    env,
    encoding: 'utf8',
    maxBuffer: 64 * 1024 * 1024,
  });
  if (r.error) {
    console.warn('[echo2vue] spawn lean:', r.error.message);
  }

  const outText = `${r.stdout || ''}\n${r.stderr || ''}`;
  const outputLines = outText.split('\n').filter((l) => l.length > 0);

  /** @type {Record<string, unknown>} */
  const latex = {};
  /** @type {Array<Record<string, unknown>>} */
  const error = [];

  tree.set_line(1);
  const modArgs = tree.args;
  const end = modArgs[modArgs.length - 1];
  const expectedLines = (codeStr.match(/\n/g) || []).length + 1;
  if (end && typeof /** @type {{ line?: number }} */ (end).line === 'number' && end.line !== expectedLines) {
    error.push({
      code: '',
      line: end.line,
      type: 'error',
      info: 'the line count of *.echo.lean file is not correct',
    });
  }

  /** @type {string[] | null} */
  let echo_codes = null;
  const ensureEchoCodes = () => {
    if (!echo_codes) {
      echo_codes = fs.readFileSync(leanEchoFile, 'utf8').split(/\r?\n/);
    }
    return echo_codes;
  };

  for (const jsonline of outputLines) {
    let parsed = null;
    try {
      parsed = JSON.parse(jsonline);
    } catch {
      parsed = null;
    }
    if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
      tree.decode(parsed, latex);
      continue;
    }
    const m = jsonline.match(DIAG_RE);
    if (m) {
      const lineNum = parseInt(m[2], 10);
      const col = parseInt(m[3], 10);
      const ec = ensureEchoCodes();
      const code = ec[lineNum - 1] ?? '';
      error.push({
        code,
        line: lineNum,
        col: col - 2,
        type: m[4],
        info: m[5],
      });
    } else if (error.length) {
      const prev = error[error.length - 1];
      prev.info = `${prev.info}\n${jsonline}`;
    }
  }

  for (const node of tree.traverse()) {
    if (node instanceof LeanTactic && node.tacticName === 'echo') {
      const ln = /** @type {{ line?: unknown }} */ (node).line;
      if (Number.isInteger(ln)) {
        const key = String(ln);
        if (!Object.prototype.hasOwnProperty.call(latex, key)) {
          latex[key] = null;
        }
        /** @type {{ line: unknown }} */ (node).line = latex[key];
      }
    }
  }

  const latexKeys = Object.keys(latex)
    .map((k) => Number(k))
    .filter((k) => Number.isFinite(k));

  const indicesToDelete = [];
  const echoLines = ensureEchoCodes();
  for (let i = 0; i < error.length; i++) {
    const err = error[i];
    const line = /** @type {number} */ (err.line);
    const code = String(err.code ?? '');
    if (/^ +echo /.test(code)) {
      if (err.type === 'error' && err.info === 'No goals to be solved') {
        err.code = echoLines[line - 1] ?? '';
      } else {
        indicesToDelete.push(i);
        continue;
      }
    }
    err.line = line - latexKeys.filter((key) => key < line).length - 1;
  }
  for (const i of indicesToDelete.sort((a, b) => b - a)) {
    error.splice(i, 1);
  }

  tree.args.shift();
  const modify = { value: false };
  const syntax = {};
  const codes = tree.render2vue(true, modify, syntax);
  codes.error.push(...error);
  if (opts.module != null) codes.module = opts.module;
  return codes;
}
