/**
 * Run Lean on a module and return the echoed render payload.
 * Runs from repo root via subprocess `cwd` (no `process.chdir`).
 * Subprocesses are async so the Node event loop can serve other HTTP requests while Lean runs.
 */
import fs from 'fs';
import path from 'path';
import { exec, spawn } from 'child_process';
import { promisify } from 'util';
import { REPO_ROOT } from './modulePath.mjs';
import { leanEchoPath } from './fetchLemmaMysql.mjs';
import { Lean, LeanModule, LeanTactic, LeanToken } from '../../js/parser/lean.js';
import { assertEchoSourceLines, traceEchoSource, withEchoAxiomsAttr } from './assert.mjs';
import { completeAxiomMessage, extractBareAxiomReports, splitAxiomReports } from './lint/axiomRules.mjs';

const execAsync = promisify(exec);

/** A parser fault is an error diagnostic, not a style warning and not a crash. */
function internalParserError(err) {
  const message = err instanceof Error ? err.message : String(err);
  const info = message.startsWith('internal parser error:')
    ? message
    : `internal parser error: ${message}`;
  return { code: '', line: 0, col: 0, type: 'error', info };
}

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

export function get_lake_path() {
  if (process.env.LEAN_LAKE_PATH) return process.env.LEAN_LAKE_PATH;
  const home = process.env.USERPROFILE || process.env.HOME || '';
  const exe = process.platform === 'win32' ? 'lake.exe' : 'lake';
  return path.join(home, '.elan', 'bin', exe);
}

/** @param {string} repoRoot */
export function get_lean_env(repoRoot) {
  const pkgsDir = path.join(repoRoot, '.lake', 'packages');
  let repository = fs.readdirSync(pkgsDir).filter((x) => x !== '.' && x !== '..');
  const cwdUnix = repoRoot.replace(/\\/g, '/');
  const env = { ...process.env };
  env.GIT_CONFIG_COUNT = String(repository.length);
  repository.forEach((directory, index) => {
    env[`GIT_CONFIG_KEY_${index}`] = 'safe.directory';
    env[`GIT_CONFIG_VALUE_${index}`] = `${cwdUnix}/.lake/packages/${directory}`;
  });
  return env;
}

/** Local lake packages whose `.lean` sources live in this repo (not Mathlib). */
const LOCAL_IMPORT_PREFIXES = [
  'Lemma.',
  'Def.', 'Theorem.', 'Instance.', 'Class.', 'Structure.', 'Abbrev.',
  'Notation.', 'Inductive.', 'Syntax.', 'Macro.', 'Initialize.',
];

/**
 * @param {string} pkg dotted module name
 */
function isLocalRepoImport(pkg) {
  return LOCAL_IMPORT_PREFIXES.some((p) => pkg === p.slice(0, -1) || pkg.startsWith(p));
}

/**
 * @param {string} pkg
 * @param {string} repoRoot
 * @returns {{ missing: boolean, mtimeStale: boolean, leanFs: string, olean: string }}
 */
function oleanStatus(pkg, repoRoot) {
  const moduleSlash = pkg.replace(/\./g, '/');
  const olean = path.join(repoRoot, '.lake', 'build', 'lib', 'lean', `${moduleSlash}.olean`);
  const leanFs = path.join(repoRoot, `${moduleSlash}.lean`);
  const out = { missing: false, mtimeStale: false, leanFs, olean };
  try {
    if (!fs.existsSync(leanFs)) return out; // not a repo-local source we can build
    if (!fs.existsSync(olean)) {
      out.missing = true;
      return out;
    }
    if (fs.statSync(olean).mtimeMs < fs.statSync(leanFs).mtimeMs) out.mtimeStale = true;
  } catch {
    out.missing = true;
  }
  return out;
}

/**
 * Whether echo2vue should `lake build` this import.
 * Lemma: missing or mtime-stale (proofs change often).
 * stdlib/torch: missing only — lake uses content hashes; bulk file touches
 * otherwise force-rebuild the whole graph and drown the UI in false failures.
 * @param {string} pkg
 * @param {string} repoRoot
 */
function isOleanStale(pkg, repoRoot) {
  const st = oleanStatus(pkg, repoRoot);
  if (st.missing) return true;
  if (pkg.startsWith('Lemma.') && st.mtimeStale) return true;
  return false;
}

/** True only when the `.olean` file is absent (not merely mtime-stale). */
function isOleanMissing(pkg, repoRoot) {
  return oleanStatus(pkg, repoRoot).missing;
}

/**
 * @param {InstanceType<typeof LeanModule>} tree
 * @param {string} repoRoot
 * @returns {string[]} stale dotted module names (unique, import order)
 */
function collectStaleLocalImports(tree, repoRoot) {
  /** @type {string[]} */
  const out = [];
  const seen = new Set();
  for (const stmt of tree.args) {
    if (!isLeanImport(stmt)) continue;
    const pkg = importPackageString(stmt);
    if (!isLocalRepoImport(pkg)) continue;
    if (seen.has(pkg)) continue;
    if (!isOleanStale(pkg, repoRoot)) continue;
    seen.add(pkg);
    out.push(pkg);
  }
  // echo2vue always injects this; ensure it is built even if parse order differs
  if (!seen.has('Syntax.Tactic.Echo') && isOleanStale('Syntax.Tactic.Echo', repoRoot)) {
    out.unshift('Syntax.Tactic.Echo');
  }
  return out;
}

/**
 * Pull Lean diagnostic lines out of `lake build` stdout/stderr for the UI.
 * @param {string} text
 * @returns {{ code: string, line: number, col: number, type: string, info: string }[]}
 */
function parseLakeBuildDiagnostics(text) {
  /** @type {{ code: string, line: number, col: number, type: string, info: string }[]} */
  const error = [];
  const lines = String(text || '').split('\n');
  for (let i = 0; i < lines.length; i++) {
    const jsonline = lines[i];
    // `lake env lean`:  path.lean:LINE:COL: error: msg
    let m = jsonline.match(/^(.+\.lean):(\d+):(\d+): (\w+)(\([^()]+\))?: (.+)$/);
    // `lake build`:     error: path.lean:LINE:COL: msg  (msg may continue on following lines)
    if (!m) {
      m = jsonline.match(/^(error|warning|info): (.+\.lean):(\d+):(\d+): (.+)$/);
      if (m) {
        const type = m[1];
        const file = m[2];
        const line = parseInt(m[3], 10);
        const col = parseInt(m[4], 10);
        let info = m[5];
        while (
          i + 1 < lines.length &&
          lines[i + 1] &&
          !/^(\u2716|✔|ℹ|⚠|error:|warning:|info:|Some required|Build |note:)/.test(lines[i + 1]) &&
          !/^(.+\.lean):\d+:\d+:/.test(lines[i + 1])
        ) {
          i += 1;
          info += `\n${lines[i]}`;
        }
        error.push({
          code: file,
          line,
          col: Math.max(0, col - 2),
          type,
          info,
        });
        continue;
      }
    }
    if (!m) continue;
    error.push({
      code: '',
      line: parseInt(m[2], 10),
      col: Math.max(0, parseInt(m[3], 10) - 2),
      type: m[4] + (m[5] ?? ''),
      info: m[6],
    });
  }
  // lake summary line: "Some required targets logged failures:\n- Foo\n- Bar"
  const failIdx = lines.findIndex((l) => /Some required targets logged failures/.test(l));
  if (failIdx >= 0) {
    const targets = [];
    for (let j = failIdx + 1; j < lines.length; j++) {
      const tm = lines[j].match(/^- (.+)$/);
      if (!tm) break;
      targets.push(tm[1].trim());
    }
    if (targets.length) {
      error.unshift({
        code: '',
        line: 1,
        col: 0,
        type: 'error',
        info: `lake build failed for required target(s): ${targets.join(', ')}`,
      });
    }
  }
  return error;
}

const SPAWN_MAX_BUFFER = 64 * 1024 * 1024;

/**
 * Like `spawnSync` for `lake env lean …` but non-blocking.
 * @param {string} command
 * @param {string[]} args
 * @param {{ cwd: string; env: NodeJS.ProcessEnv; windowsHide?: boolean }}
 * @returns {Promise<{ stdout: string; stderr: string; error: Error | null; status?: number | null }>}
 */
export function spawnLakeLean(command, args, { cwd, env, windowsHide = true }) {
  return new Promise((resolve) => {
    const child = spawn(command, args, {
      cwd,
      env,
      windowsHide,
    });
    let stdout = '';
    let stderr = '';
    let outBytes = 0;
    let settled = false;

    /** @param {string} chunk */
    function onChunk(chunk) {
      outBytes += Buffer.byteLength(chunk, 'utf8');
      if (outBytes > SPAWN_MAX_BUFFER && !settled) {
        settled = true;
        child.kill();
        resolve({
          stdout,
          stderr,
          error: new Error('spawn maxBuffer exceeded'),
        });
      }
    }

    /** @param {{ stdout: string; stderr: string; error: Error | null; status?: number | null }} result */
    function finish(result) {
      if (settled) return;
      settled = true;
      resolve(result);
    }

    child.stdout?.setEncoding('utf8');
    child.stderr?.setEncoding('utf8');
    child.stdout?.on('data', (chunk) => {
      onChunk(chunk);
      stdout += chunk;
    });
    child.stderr?.on('data', (chunk) => {
      onChunk(chunk);
      stderr += chunk;
    });
    child.on('error', (err) => {
      console.warn('[echo2vue] spawn lean:', err.message);
      finish({ stdout, stderr, error: err });
    });
    child.on('close', (status) => {
      finish({ stdout, stderr, error: null, status });
    });
  });
}

export function prepareEchoSource(tree) {
  if (!(tree instanceof LeanModule)) throw new Error('prepareEchoSource expects LeanModule');

  tree.relocate_last_comment();
  tree.echo();

  // Lean 4.9 `module` files may only import `module` files, and `Syntax.Tactic.Echo` is not one.
  // Echo the same declarations as a plain file: drop the header and the `public` modifiers.
  const [header] = tree.args;
  if (header instanceof LeanToken && header.text === 'module') {
    const headerLine = header.line ?? 1;
    tree.kwargs.moduleFile = true;
    tree.args.shift();
    Lean.shiftLines(tree, headerLine + 1, -1);
    for (const stmt of tree.args) {
      if (isLeanImport(stmt)) stmt.kwargs.accessibility = undefined;
    }
  }

  // Keep parser coordinates separate from positions in the rewritten Echo file.
  const parserErrors = [];
  const recordParserError = (err) => {
    parserErrors.push(internalParserError(err));
  };
  let codeStr = '';
  const echoPositions = new Map();
  try {
    const trace = traceEchoSource(tree);
    const { source } = trace;
    let prefix = '\uE000echo';
    while (source.includes(prefix)) prefix += '_';
    const nodes = [...new Set([...tree.traverse()].filter(
      node => node instanceof LeanTactic && node.tacticName === 'echo',
    ))];
    const restore = [];
    let marked;
    try {
      nodes.forEach((node, index) => {
        const original = node.strFormat;
        const descriptor = Object.getOwnPropertyDescriptor(node, 'strFormat');
        Object.defineProperty(node, 'strFormat', {
          configurable: true,
          value() { return prefix + index + '\uE001' + original.call(this); },
        });
        restore.push(() => {
          if (descriptor) Object.defineProperty(node, 'strFormat', descriptor);
          else delete node.strFormat;
        });
      });
      marked = String(tree);
    } finally {
      for (const reset of restore) reset();
    }

    const lines = marked.split('\n');
    const marker = new RegExp(prefix + '(\\d+)\uE001(?=echo\\b)', 'g');
    const unmarked = lines.map((line, index) => line.replace(marker, (_, id) => {
      const node = nodes[Number(id)];
      if (!node || echoPositions.has(node)) {
        throw new Error('Invalid Echo source marker on line ' + (index + 1));
      }
      echoPositions.set(node, index + 1);
      return '';
    })).join('\n');
    if (unmarked !== source || echoPositions.size !== nodes.length) {
      throw new Error('Echo line map does not match rendered source');
    }

    codeStr = withEchoAxiomsAttr(source);
    if (codeStr.split('\n').length !== lines.length) {
      recordParserError(new Error('Echo attribute rewrite changed the line count'));
    }
    try {
      assertEchoSourceLines(tree, codeStr, trace);
    } catch (e) {
      recordParserError(e);
    }
    for (const [node, line] of echoPositions) {
      if (node.line !== line) {
        recordParserError(new Error('Echo tactic position disagrees with AST layout on line ' + line));
      }
    }
  } catch (e) {
    recordParserError(e);
    if (!codeStr) {
      try {
        codeStr = withEchoAxiomsAttr(String(tree));
      } catch (e2) {
        recordParserError(e2);
      }
    }
  }
  return { codeStr, echoPositions, parserErrors };
}

export async function runEcho2Vue(tree, leanFileAbs, opts = {}) {
  const repoRoot = REPO_ROOT;
  const leanEchoFile = leanEchoPath(path.resolve(leanFileAbs));
  const { codeStr, echoPositions, parserErrors = [] } = prepareEchoSource(tree);

  if (codeStr) {
    if (!fs.existsSync(leanEchoFile)) {
      fs.mkdirSync(path.dirname(leanEchoFile), { recursive: true });
      fs.writeFileSync(leanEchoFile, '', 'utf8');
    }
    fs.writeFileSync(leanEchoFile, codeStr, 'utf8');
  }

  const lakePath = get_lake_path();
  const env = get_lean_env(repoRoot);
  /** @type {{ code: string, line: number, col: number, type: string, info: string }[]} */
  const lakeBuildErrors = [];
  const staleImports = codeStr ? collectStaleLocalImports(tree, repoRoot) : [];
  if (staleImports.length) {
    const quoted = staleImports.map((n) => `"${n.replace(/"/g, '\\"')}"`).join(' ');
    const cmd = `"${lakePath}" build ${quoted}`;
    try {
      await execAsync(cmd, {
        cwd: repoRoot,
        env,
        windowsHide: true,
        shell: true,
        maxBuffer: SPAWN_MAX_BUFFER,
      });
    } catch (e) {
      const stdout = e?.stdout != null ? String(e.stdout) : '';
      const stderr = e?.stderr != null ? String(e.stderr) : '';
      const combined = `${stdout}\n${stderr}\n${e?.message || e}`;
      console.warn('[echo2vue] lake build failed for:', staleImports.join(', '));
      console.warn('[echo2vue] lake build:', (e?.message || e || '').toString().slice(0, 500));
      const diags = parseLakeBuildDiagnostics(combined);
      if (diags.length) {
        lakeBuildErrors.push(...diags);
      } else {
        lakeBuildErrors.push({
          code: '',
          line: 1,
          col: 0,
          type: 'error',
          info:
            `lake build failed for stale imports [${staleImports.join(', ')}]: ` +
            (stderr || stdout || e?.message || 'unknown error').toString().slice(0, 2000),
        });
      }
      // Truly missing oleans after a failed build (ignore mtime-only staleness)
      for (const pkg of staleImports) {
        if (!isOleanMissing(pkg, repoRoot)) continue;
        const olean = oleanStatus(pkg, repoRoot).olean;
        lakeBuildErrors.push({
          code: `import ${pkg}`,
          line: 1,
          col: 0,
          type: 'error',
          info:
            `dependency ${pkg} has no .olean after lake build (expected ${olean}). ` +
            `Fix Lean errors in that module or its deps (see lake build diagnostics above) and rebuild.`,
        });
      }
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
  const r = codeStr
    ? await spawnLakeLean(lakePath, leanArgs, {
      cwd: repoRoot,
      env,
      windowsHide: true,
    })
    : { stdout: '', stderr: '', error: null, status: 0 };
  if (r.error) {
    console.warn('[echo2vue] spawn lean:', r.error.message);
  }

  const outText = `${r.stdout || ''}\n${r.stderr || ''}`;
  const rawLines = outText.split('\n').filter((l) => l.length > 0);
  // `'decl' depends on axioms: […]` has no file:line:col. Pull it out before the
  // diagnostic loop so a transitive `sorryAx` is not dropped on a clean compile.
  const { rest: outputLines, reports: bareAxiomReports } = extractBareAxiomReports(rawLines);

  const latex = {};
  const structs = {};
  const error = [];

  let echo_codes = null;
  const ensureEchoCodes = () => {
    if (!echo_codes) {
      echo_codes = fs.readFileSync(leanEchoFile, 'utf8').split(/\r?\n/);
    }
    return echo_codes;
  };

  for (let i = 0; i < outputLines.length; i++) {
    const jsonline = outputLines[i];
    // lake noise (e.g. `warning: proofwidgets: repository '…' has local changes`) is not a Lean diagnostic
    if (/^warning: [^:]+: repository .* has local changes/.test(jsonline)) continue;
    let parsed = null;
    try {
      parsed = JSON.parse(jsonline);
    } catch {
      parsed = null;
    }
    if (parsed && typeof parsed === 'object' && !Array.isArray(parsed)) {
      tree.decode(parsed, latex, structs);
      continue;
    }
    const m = jsonline.match(/^(.+\.lean):(\d+):(\d+): (\w+)(\([^()]+\))?: (.+)$/);
    if (m) {
      const lineNum = parseInt(m[2], 10);
      const col = parseInt(m[3], 10);
      const ec = ensureEchoCodes();
      const code = ec[lineNum - 1] ?? '';
      // A wrapped axiom list is one message, not a continuation of the previous diagnostic.
      const taken = completeAxiomMessage(outputLines, i, m[6]);
      error.push({
        code,
        line: lineNum,
        col: col - 2,
        type: m[4] + (m[5] ?? ''),
        info: taken.info,
      });
      i = taken.next - 1;
    } else if (error.length) {
      const prev = error[error.length - 1];
      prev.info = `${prev.info}\n${jsonline}`;
    }
  }

  if (bareAxiomReports.length) {
    const ec = ensureEchoCodes();
    const attrIdx = ec.findIndex((l) => /@\[[^\]]*\baxioms\b/.test(l));
    const lineNum = attrIdx >= 0 ? attrIdx + 1 : 1;
    for (const info of bareAxiomReports) {
      error.push({
        code: attrIdx >= 0 ? ec[attrIdx] : '',
        line: lineNum,
        col: 1,
        type: 'info',
        info,
      });
    }
  }

  for (const [node, line] of echoPositions) {
    const key = String(line);
    if (!Object.prototype.hasOwnProperty.call(latex, key)) latex[key] = null;
    node.echoLatex = latex[key];
    if (Object.prototype.hasOwnProperty.call(structs, key)) node.searchStruct = structs[key];
  }

  const latexKeys = Object.keys(latex)
    .map((k) => Number(k))
    .filter((k) => Number.isFinite(k));

  const indicesToDelete = [];
  const echoLines = ensureEchoCodes();
  for (let i = 0; i < error.length; i++) {
    const err = error[i];
    const {line} = err;
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

  // Drop the synthetic `import Syntax.Tactic.Echo` from the rendered payload: index 0 for a plain
  // file, right after the `module` header in a Lean 4.9 module file.
  const echoImportIdx = tree.args.findIndex(
    (a) => isLeanImport(a) && importPackageString(a) === 'Syntax.Tactic.Echo',
  );
  if (echoImportIdx >= 0) tree.args.splice(echoImportIdx, 1);
  else tree.args.shift();
  tree.restoreMaxHeartbeats();

  const modify = { value: false };
  const syntax = {};
  const codes = tree.render2vue(true, modify, syntax);
  // Prefer concrete lake-build diagnostics over Lean's misleading line-1
  // "olean does not exist" attributed to `import Syntax.Tactic.Echo`.
  const coveredMissing = new Set(
    lakeBuildErrors
      .map((e) => {
        const m = String(e.info || '').match(/dependency (\S+) has no \.olean/);
        return m ? m[1] : null;
      })
      .filter(Boolean)
  );
  const leanErrors = error.filter((e) => {
    const info = String(e.info || '');
    const m = info.match(/object file '.*?\.olean' of module (\S+) does not exist/);
    if (m && coveredMissing.has(m[1])) return false;
    return true;
  });
  // `@[axioms]` info is not a Lean error. Allowed names stay silent; anything else is a style warning.
  const axiomSplit = splitAxiomReports(leanErrors);
  codes.error.push(...parserErrors, ...lakeBuildErrors, ...axiomSplit.errors);
  if (axiomSplit.warnings.length) codes.warning = axiomSplit.warnings;
  if (opts.module != null) codes.module = opts.module;
  return codes;
}
