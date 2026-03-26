#!/usr/bin/env node
/**
 * Print `Lean*` class declaration order: PHP (`lean.php`) vs JS (`lean.js`).
 * Use for side-by-side comparison; full JS reorder to match PHP is blocked by
 * JS init order (e.g. `LeanCaret` references types declared later).
 */
import fs from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const php = fs.readFileSync(join(root, 'php/parser/lean.php'), 'utf8');
const js = fs.readFileSync(join(root, 'static/js/parser/lean.js'), 'utf8');

const phpRe = /(?:^|\n)(?:abstract )?class (Lean\w+)/g;
const jsRe = /(?:^|\n)(?:export )?class (Lean\w+)/g;

function collect(re, s) {
    const out = [];
    let m;
    while ((m = re.exec(s))) out.push(m[1]);
    return out;
}

const phpOrder = [...new Set(collect(phpRe, php))];
const jsOrder = [...new Set(collect(jsRe, js))];
const jsIdx = new Map();
jsOrder.forEach((n, i) => {
    if (!jsIdx.has(n)) jsIdx.set(n, i);
});

const maxLen = Math.max(phpOrder.length, jsOrder.length);
console.log('idx\tPHP (lean.php)\t\t\tJS (lean.js)');
console.log('-'.repeat(72));
for (let i = 0; i < maxLen; i++) {
    const p = phpOrder[i] ?? '';
    const j = jsOrder[i] ?? '';
    const mark =
        p && j && p !== j
            ? phpOrder.indexOf(j) !== i
                ? ' *'
                : ''
            : '';
    console.log(`${String(i).padStart(3)}\t${(p || '—').padEnd(28)}\t${(j || '—').padEnd(28)}${mark}`);
}
console.log('');
console.log('* = JS name at this line differs from PHP name at this line (order mismatch).');
console.log(`PHP unique: ${phpOrder.length}, JS unique: ${jsOrder.length}`);
const ps = new Set(phpOrder);
const jsS = new Set(jsOrder);
const phpOnly = phpOrder.filter((n) => !jsS.has(n));
const jsOnly = jsOrder.filter((n) => !ps.has(n));
if (phpOnly.length) console.log('PHP only:', phpOnly.join(', '));
if (jsOnly.length) console.log('JS only:', jsOnly.join(', '));
