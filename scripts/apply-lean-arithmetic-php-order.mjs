#!/usr/bin/env node
/**
 * Rebuild the LeanArithmetic + related block in `static/js/parser/lean.js` to match
 * `php/parser/lean.php` declaration order. Inserts `LeanArgs*` before `LeanBitOr` (required for JS).
 *
 * Run from repo root: `node scripts/apply-lean-arithmetic-php-order.mjs`
 */
import fs from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const jsPath = join(root, 'static/js/parser/lean.js');
const src = fs.readFileSync(jsPath, 'utf8');

/** @param {string} s @param {string} className @param {boolean} exportClass */
function extractClassBlock(s, className, exportClass = true) {
    const needle = exportClass ? `export class ${className} extends ` : `class ${className} extends `;
    const idx = s.indexOf(needle);
    if (idx < 0) throw new Error(`Missing ${needle}`);
    let start = idx;
    const prevNl = s.lastIndexOf('\n', idx - 1);
    const prevComment = s.lastIndexOf('\n/**', idx);
    if (prevComment > prevNl && prevComment < idx) start = prevComment + 1;

    const open = s.indexOf('{', idx);
    let depth = 0;
    let i = open;
    for (; i < s.length; i++) {
        const c = s[i];
        if (c === '{') depth++;
        else if (c === '}') {
            depth--;
            if (depth === 0) {
                i++;
                break;
            }
        }
    }
    return { text: s.slice(start, i), start, end: i };
}

const phpArithmeticAndArgs = [
    'LeanAdd',
    'LeanSub',
    'LeanMul',
    'Lean_times',
    'LeanMatMul',
    'Lean_bullet',
    'Lean_odot',
    'Lean_otimes',
    'Lean_oplus',
    'LeanDiv',
    'LeanFDiv',
    'LeanBitAnd',
    'LeanBitwiseAnd',
    'LeanBitwiseXor',
    'LeanArgsCommaSeparated',
    'LeanArgsNewLineSeparated',
    'LeanArgsCommaNewLineSeparated',
    'LeanArgsSemicolonSeparated',
    'LeanBitOr',
    'LeanBitwiseOr',
    'LeanPow',
    // Match php/parser/lean.php order after LeanPow (ll…Modular before Construct…Append).
    'Lean_ll',
    'Lean_lll',
    'Lean_gg',
    'Lean_ggg',
    'LeanModular',
    'LeanConstruct',
    'LeanVConstruct',
    'LeanAppend',
    'Lean_sqcup',
    'Lean_sqcap',
    'Lean_cdotp',
    'Lean_circ',
    'Lean_blacktriangleright',
];

const binarySymbols = [
    'Lean_ominus',
    'Lean_oslash',
    'Lean_circledcirc',
    'Lean_circledast',
    'Lean_circleeq',
    'Lean_circleddash',
    'Lean_boxplus',
    'Lean_boxminus',
    'Lean_boxtimes',
    'Lean_dotsquare',
    'LeanEDiv',
];

// Region: first `LeanAdd` … last `LeanEDiv` before `LeanSetOperator` (marker comment may be absent after prior runs).
const regionStartMarker = 'export class LeanAdd extends LeanArithmetic';
let regionStart = src.indexOf(regionStartMarker);
if (regionStart < 0) throw new Error(`Missing ${regionStartMarker}`);
const prevComment = src.lastIndexOf('\n/**', regionStart);
const prevArithmetic = src.lastIndexOf('\nexport class LeanArithmetic extends', regionStart);
if (prevComment > prevArithmetic && prevComment >= 0) regionStart = prevComment + 1;

const regionEnd = src.indexOf(
    '/** Set-theoretic binary (`\\\\`, `∪`, `∩`); abstract base like `LeanSetOperator`. */',
);
if (regionEnd < 0 || regionEnd <= regionStart) {
    throw new Error('Could not find Set-theoretic / LeanSetOperator region marker');
}

const extracted = new Map();
for (const name of [...phpArithmeticAndArgs, ...binarySymbols]) {
    try {
        extracted.set(name, extractClassBlock(src, name).text);
    } catch (e) {
        console.warn(String(e.message));
    }
}

let middle = '';
for (const name of phpArithmeticAndArgs) {
    const t = extracted.get(name);
    if (!t) throw new Error(`Missing extracted block: ${name}`);
    middle += t + '\n\n';
}
for (const name of binarySymbols) {
    const t = extracted.get(name);
    if (t) middle += t + '\n\n';
}

const newSrc = src.slice(0, regionStart) + middle + src.slice(regionEnd);
fs.writeFileSync(jsPath, newSrc);
console.log('Updated', jsPath);
