/**
 * Recursively walk `Lemma/` for `.lean` files (skips `*.echo.lean`), map each file
 * to a module name (`Lemma/A/B.lean` → `A.B`), then run the same proof comparison as
 * compare-lemma-proof-node-php.mjs (Node vs PHP lemma HTML).
 *
 * Usage:
 *   node scripts/scan-lemma-proof-node-php.mjs [--limit=N] [--fail-fast] [--verbose] [--include-latex]
 *
 * Env: same as compare script (LEAN_NODE_LEMMA_BASE, LEAN_PHP_LEMMA_BASE).
 * By default only proof.by[].lean is compared; --include-latex or
 * LEAN_PROOF_COMPARE_INCLUDE_LATEX=1 restores full step comparison.
 *
 * Note: modules that use the `#` filename convention (see moduleToLeanPath)
 * are not reconstructed here; only dot-separated paths are scanned.
 *
 * Exit: 0 all same, 1 any diff or error
 */
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import process from 'process';
import {
  compareLemmaProof,
  lemmaProofCompareBases,
} from './lemmaProofNodePhpCore.mjs';

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO_ROOT = path.join(__dirname, '..');
const LEMMA_ROOT = path.join(REPO_ROOT, 'Lemma');

function parseArgs(argv) {
  let limit = Infinity;
  let failFast = false;
  let verbose = false;
  let includeLatex = false;
  const rest = [];
  for (const a of argv) {
    if (a === '--fail-fast') failFast = true;
    else if (a === '--verbose' || a === '-v') verbose = true;
    else if (a === '--include-latex') includeLatex = true;
    else if (a.startsWith('--limit=')) {
      const n = Number(a.slice('--limit='.length));
      if (Number.isFinite(n) && n > 0) limit = n;
    } else if (!a.startsWith('-')) rest.push(a);
  }
  return { limit, failFast, verbose, includeLatex, rest };
}

/**
 * @param {string} lemmaRoot absolute Lemma/
 * @param {string} absPath absolute path to *.lean
 */
function leanFileToModule(lemmaRoot, absPath) {
  const rel = path.relative(lemmaRoot, absPath);
  const noExt = rel.replace(/\.lean$/i, '');
  return noExt.split(path.sep).join('.');
}

/** @param {string} dir */
function collectLeanFiles(dir) {
  /** @type {string[]} */
  const out = [];
  if (!fs.existsSync(dir)) {
    return out;
  }
  const stack = [dir];
  while (stack.length) {
    const d = /** @type {string} */ (stack.pop());
    let entries;
    try {
      entries = fs.readdirSync(d, { withFileTypes: true });
    } catch {
      continue;
    }
    for (const ent of entries) {
      const p = path.join(d, ent.name);
      if (ent.isDirectory()) {
        stack.push(p);
      } else if (ent.isFile() && /\.lean$/i.test(ent.name)) {
        if (/\.echo\.lean$/i.test(ent.name)) continue;
        out.push(p);
      }
    }
  }
  return out;
}

const { limit, failFast, verbose, includeLatex } = parseArgs(
  process.argv.slice(2)
);

if (!fs.existsSync(LEMMA_ROOT)) {
  console.error(`Lemma folder not found: ${LEMMA_ROOT}`);
  process.exit(1);
}

let files = collectLeanFiles(LEMMA_ROOT);
files.sort((a, b) => a.localeCompare(b, 'en'));

/** @type {{ module: string, path: string }[]} */
const jobs = [];
for (const f of files) {
  jobs.push({ module: leanFileToModule(LEMMA_ROOT, f), path: f });
}

const toRun = jobs.slice(0, limit);
const bases = { ...lemmaProofCompareBases(), includeLatex };

console.log(`Lemma root: ${LEMMA_ROOT}`);
console.log(
  `Comparing ${toRun.length} module(s) (of ${jobs.length} lean files) Node vs PHP…`
);
console.log(
  `Mode: ${includeLatex ? 'lean + latex' : 'lean only (set --include-latex for full)'}`
);
console.log(`Node base: ${bases.nodeBase}`);
console.log(`PHP base:  ${bases.phpBase}`);
if (limit < jobs.length) {
  console.log(`(--limit=${limit})`);
}

let same = 0;
let diff = 0;
let err = 0;
/** @type {string[]} */
const diffList = [];
/** @type {string[]} */
const errList = [];

for (let i = 0; i < toRun.length; i++) {
  const { module: mod } = toRun[i];
  if (verbose) {
    console.log(`[${i + 1}/${toRun.length}] ${mod}`);
  }

  const r = await compareLemmaProof(mod, bases);
  if (r.code === 0) {
    same++;
  } else if (r.code === 1) {
    diff++;
    diffList.push(`${mod}: ${r.message}`);
    console.error(`DIFF  ${mod}: ${r.message}`);
    if (failFast) break;
  } else {
    err++;
    errList.push(`${mod}: ${r.message}`);
    console.error(`ERROR ${mod}: ${r.message}`);
    if (failFast) break;
  }
}

console.log('');
console.log('--- summary ---');
console.log(`same:  ${same}`);
console.log(`diff:  ${diff}`);
console.log(`error: ${err}`);
console.log(`total: ${same + diff + err}`);

const exitCode = diff > 0 || err > 0 ? 1 : 0;
if (exitCode === 0) {
  console.log(
    'All compared lemmas: proof content consistent (Node vs PHP) for the chosen mode.'
  );
} else {
  if (diffList.length && !verbose) {
    console.error('\nDiff modules:');
    for (const line of diffList) console.error(' ', line);
  }
  if (errList.length && !verbose) {
    console.error('\nError modules:');
    for (const line of errList) console.error(' ', line);
  }
}

process.exit(exitCode);
