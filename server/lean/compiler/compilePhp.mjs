/**
 * Runs the real PHP `compile` → `render2vue(false)` via CLI (same output as `php/lemma.php`).
 */
import { spawnSync } from 'child_process';
import path from 'path';
import { fileURLToPath } from 'url';
import fs from 'fs';
import { REPO_ROOT } from '../modulePath.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const BRIDGE = path.join(__dirname, '..', 'php-bridge', 'render2vue.php');
const BRIDGE_ECHO2VUE = path.join(__dirname, '..', 'php-bridge', 'echo2vue.php');

function findPhp() {
  const fromEnv = process.env.PHP_PATH || process.env.PHP_BIN;
  if (fromEnv && fs.existsSync(fromEnv)) return fromEnv;

  const common = [
    'C:\\php\\php.exe',
    'C:\\wamp64\\bin\\php\\php8.3.6\\php.exe',
    'C:\\wamp64\\bin\\php\\php8.2.18\\php.exe',
    'C:\\xampp\\php\\php.exe',
    'C:\\laragon\\bin\\php\\php-8.3.12-Win32-vs16-x64\\php.exe',
  ];
  for (const p of common) {
    if (fs.existsSync(p)) return p;
  }

  if (process.platform === 'win32') {
    const r = spawnSync(
      process.env.SystemRoot
        ? `${process.env.SystemRoot}\\System32\\where.exe`
        : 'where.exe',
      ['php'],
      { encoding: 'utf-8' }
    );
    if (r.status === 0 && r.stdout) {
      const first = r.stdout.split(/\r?\n/).map((s) => s.trim()).find(Boolean);
      if (first && fs.existsSync(first)) return first;
    }
  }

  return 'php';
}

export function phpAvailable() {
  const php = findPhp();
  const r = spawnSync(php, ['-v'], { encoding: 'utf-8', windowsHide: true });
  if (r.error && r.error.code === 'ENOENT') return false;
  return r.status === 0;
}

/**
 * @param {string} source full `.lean` file text
 * @param {{ cwd?: string }} [opts]
 * @returns {object} same shape as Vue `createApp('render', …)`
 */
export function render2vueViaPhp(source, opts = {}) {
  const cwd = opts.cwd || REPO_ROOT;
  const php = findPhp();
  const r = spawnSync(php, [BRIDGE], {
    input: source,
    encoding: 'utf-8',
    maxBuffer: 100 * 1024 * 1024,
    cwd,
    windowsHide: true,
  });
  if (r.error) throw r.error;
  if (r.status !== 0) {
    throw new Error(
      (r.stderr && r.stderr.trim()) ||
        (r.stdout && r.stdout.trim()) ||
        `PHP render2vue exited with ${r.status}`
    );
  }
  return JSON.parse(r.stdout);
}

/**
 * Runs PHP `LeanModule::echo2vue($absLeanPath)` (writes `*.echo.lean`, runs `lake` + `lean`, merges goal JSON).
 * Same JSON as `php/request/echo.php` / `compile($src)->echo2vue($path)`.
 *
 * @param {string} absLeanPath absolute path to a `.lean` file under the repo (e.g. from `moduleToLeanPath`)
 * @param {{ cwd?: string }} [opts]
 * @returns {object} Vue payload with `echo`-merged proof LaTeX
 */
export function echo2vueViaPhp(absLeanPath, opts = {}) {
  const cwd = opts.cwd || REPO_ROOT;
  const resolved = path.resolve(absLeanPath);
  if (!fs.existsSync(resolved)) {
    throw new Error(`Lean file not found: ${resolved}`);
  }
  const php = findPhp();
  const r = spawnSync(php, [BRIDGE_ECHO2VUE, resolved], {
    encoding: 'utf-8',
    maxBuffer: 100 * 1024 * 1024,
    cwd,
    windowsHide: true,
  });
  if (r.error) throw r.error;
  if (r.status !== 0) {
    throw new Error(
      (r.stderr && r.stderr.trim()) ||
        (r.stdout && r.stdout.trim()) ||
        `PHP echo2vue exited with ${r.status}`
    );
  }
  return JSON.parse(r.stdout);
}
