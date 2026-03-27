#!/usr/bin/env node
/**
 * Compare `Lean*` class declaration order between `php/parser/lean.php` and `static/js/parser/lean.js`.
 *
 * Usage:
 *   node scripts/compare-lean-class-declarations.mjs
 *   node scripts/compare-lean-class-declarations.mjs --strict-arithmetic
 *   node scripts/compare-lean-class-declarations.mjs --around LeanBitAnd
 *
 * `--strict-arithmetic`: require JS declaration order of `class * extends LeanArithmetic` to match
 * PHP exactly (same names, same order). Exits 1 on mismatch (translation task gate).
 *
 * Global row-by-row equality of all classes is NOT required (JS groups declarations; see README Option B).
 */
import fs from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const phpPath = join(root, 'php/parser/lean.php');
const jsPath = join(root, 'static/js/parser/lean.js');

const php = fs.readFileSync(phpPath, 'utf8');
const js = fs.readFileSync(jsPath, 'utf8');

const phpAllRe = /(?:^|\n)(?:abstract )?class (Lean\w+)/g;
const jsAllRe = /(?:^|\n)(?:export )?class (Lean\w+)/g;

function collect(re, s) {
    const out = [];
    let m;
    while ((m = re.exec(s))) out.push(m[1]);
    return out;
}

// PHP may use multiple spaces before `extends` (e.g. `class Lean_blacktriangleright  extends`).
const phpArithmeticRe = /(?:^|\n)class (Lean\w+)\s+extends LeanArithmetic/g;
const jsArithmeticRe = /(?:^|\n)export class (Lean\w+)\s+extends LeanArithmetic/g;

const phpOrderAll = [...new Set(collect(phpAllRe, php))];
const jsOrderAll = [...new Set(collect(jsAllRe, js))];
const phpArithmetic = collect(phpArithmeticRe, php);
const jsArithmetic = collect(jsArithmeticRe, js);

console.log('=== All Lean* classes (first occurrence order, deduped) ===');
console.log(`PHP: ${phpOrderAll.length}  JS: ${jsOrderAll.length}`);
const ps = new Set(phpOrderAll);
const jsS = new Set(jsOrderAll);
const phpOnly = phpOrderAll.filter((n) => !jsS.has(n));
const jsOnly = jsOrderAll.filter((n) => !ps.has(n));
if (phpOnly.length) console.log('PHP only:', phpOnly.join(', '));
if (jsOnly.length) console.log('JS only:', jsOnly.join(', '));

console.log('\n=== LeanArithmetic subclasses (declaration order) ===');
console.log('PHP:', phpArithmetic.join(', '));
console.log('JS: ', jsArithmetic.join(', '));

let failed = false;
if (phpArithmetic.length !== jsArithmetic.length) {
    console.error(
        `\nError: LeanArithmetic subclass count differs (PHP ${phpArithmetic.length} vs JS ${jsArithmetic.length}).`,
    );
    failed = true;
} else {
    for (let i = 0; i < phpArithmetic.length; i++) {
        if (phpArithmetic[i] !== jsArithmetic[i]) {
            console.error(
                `\nError: LeanArithmetic order mismatch at index ${i}: PHP=${phpArithmetic[i]} JS=${jsArithmetic[i]}`,
            );
            failed = true;
            break;
        }
    }
}

const argv = process.argv.slice(2);
if (argv.includes('--strict-arithmetic') && failed) {
    console.error(
        '\nRepair: reorder `export class … extends LeanArithmetic` blocks in `static/js/parser/lean.js` to match `lean.php` (see `php/parser/lean.php` LeanArithmetic subclasses).',
    );
    process.exit(1);
}

if (!argv.includes('--strict-arithmetic') && failed) {
    console.log(
        '\nNote: arithmetic order differs (see above). Run with --strict-arithmetic to fail CI, or fix lean.js.',
    );
}

// Optional neighborhood (same as print-lean-class-order)
const aroundArg = argv.find((a) => a.startsWith('--around='));
const aroundName =
    aroundArg?.slice('--around='.length) || (argv.includes('--around') ? argv[argv.indexOf('--around') + 1] : null);
if (aroundName) {
    const pi = phpOrderAll.indexOf(aroundName);
    const ji = jsOrderAll.indexOf(aroundName);
    console.log(`\n=== Around ${aroundName} (PHP idx ${pi}, JS idx ${ji}) ===`);
    const w = 6;
    for (let k = -w; k <= w; k++) {
        const p = pi >= 0 ? phpOrderAll[pi + k] : '';
        const j = ji >= 0 ? jsOrderAll[ji + k] : '';
        const mark = p && j && p === j ? '  ' : '**';
        if (p || j) console.log(`${mark} ${String(k).padStart(3)}  PHP: ${(p || '—').padEnd(28)}  JS: ${(j || '—').padEnd(28)}`);
    }
}

if (!argv.includes('--strict-arithmetic')) {
    process.exit(0);
}
process.exit(failed ? 1 : 0);
