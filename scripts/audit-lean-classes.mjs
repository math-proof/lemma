#!/usr/bin/env node
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

const pn = collect(phpRe, php);
const jn = collect(jsRe, js);
const ps = new Set(pn);
const jsSet = new Set(jn);

const phpOnly = [...new Set(pn.filter((n) => !jsSet.has(n)))].sort();
const jsOnly = [...new Set(jn.filter((n) => !ps.has(n)))].sort();

console.log('PHP Lean* classes:', pn.length);
console.log('JS  Lean* classes:', jn.length);
console.log('PHP only (no JS class name):', phpOnly.length ? phpOnly.join(', ') : '(none)');
console.log('JS only (no PHP class name):', jsOnly.length ? jsOnly.join(', ') : '(none)');

const abstractsPhp = [
    'LeanArithmetic',
    'LeanRelational',
    'LeanUnaryArithmetic',
    'LeanUnaryArithmeticPre',
    'LeanUnaryArithmeticPost',
    'LeanSyntax',
];
console.log('Abstract in PHP often mirrored in JS (not flattened):', abstractsPhp.join(', '));
console.log('Also in both: LeanLogic, LeanSetOperator (abstract bases).');

// --- Step 2: declaration order (shared classes only) ---
const jsIndex = new Map();
jn.forEach((name, i) => {
    if (!jsIndex.has(name)) jsIndex.set(name, i);
});
const sharedInPhpOrder = [...new Set(pn)].filter((n) => jsSet.has(n));
let inversions = 0;
let pairs = 0;
for (let i = 0; i < sharedInPhpOrder.length; i++) {
    for (let j = i + 1; j < sharedInPhpOrder.length; j++) {
        const a = sharedInPhpOrder[i];
        const b = sharedInPhpOrder[j];
        pairs++;
        if (jsIndex.get(a) > jsIndex.get(b)) inversions++;
    }
}
console.log('');
console.log('Step 2 (order): shared class names PHP∩JS:', sharedInPhpOrder.length);
console.log(
    '  Pairwise order vs lean.js (0 = JS matches PHP order):',
    inversions,
    'inversions of',
    pairs,
    `(~${pairs ? ((100 * inversions) / pairs).toFixed(1) : 0}% inverted)`,
);
console.log('  Note: high inversion rate is expected (JS groups by role; README Option B).');
