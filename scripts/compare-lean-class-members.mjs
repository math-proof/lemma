#!/usr/bin/env node
/**
 * Compare ordered static fields / getters / methods per `Lean*` class between
 * `php/parser/lean.php` and `static/js/parser/lean.js`.
 *
 * Usage:
 *   node scripts/compare-lean-class-members.mjs
 *   node scripts/compare-lean-class-members.mjs --class LeanBitAnd
 *   node scripts/compare-lean-class-members.mjs --strict   (exit 1 on any mismatch for shared classes)
 *   node scripts/compare-lean-class-members.mjs --arithmetic [--strict]
 *       only classes `extends LeanArithmetic` in PHP order (translation parity gate; see LeanBitAnd / bitwise cluster).
 *
 * PHP `__get` / `__set` are expanded to `get:name` / `set:name` from `case 'name':` bodies when present.
 * With `--arithmetic`, `static:input_priority` is ignored on one side when the other class body has no `public static $input_priority` (e.g. LeanBitOr).
 * Repair: align `lean.js` member order and names with PHP (see README Step 3).
 */
import fs from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const phpPath = join(root, 'php/parser/lean.php');
const jsPath = join(root, 'static/js/parser/lean.js');

const phpSrc = fs.readFileSync(phpPath, 'utf8');
const jsSrc = fs.readFileSync(jsPath, 'utf8');

const phpClassDecl =
    /(?:^|\n)((?:abstract )?)class (Lean\w+)\s+extends\s+\w+(?:\s*\{|\s*\n\s*\{)/g;
const jsClassDecl = /(?:^|\n)export class (Lean\w+)\s+extends\s+\w+\s*\{/g;
const phpArithmeticRe = /(?:^|\n)class (Lean\w+)\s+extends LeanArithmetic/g;

function collectArithmeticOrder(s) {
    const out = [];
    let m;
    while ((m = phpArithmeticRe.exec(s))) out.push(m[1]);
    return out;
}

function collectClassOrder(re, s) {
    const out = [];
    let m;
    while ((m = re.exec(s))) out.push(m[2] ?? m[1]);
    return [...new Set(out)];
}

/** Full class text from `class` / `export class` through matching closing `}`. */
function extractClassBlock(s, className, exportJs) {
    const needle = exportJs ? `export class ${className} extends ` : `class ${className} extends `;
    const idx = s.indexOf(needle);
    if (idx < 0) return null;
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
    return s.slice(start, i);
}

function innerBody(classBlock) {
    const open = classBlock.indexOf('{');
    if (open < 0) return '';
    let depth = 0;
    for (let i = open; i < classBlock.length; i++) {
        if (classBlock[i] === '{') depth++;
        else if (classBlock[i] === '}') {
            depth--;
            if (depth === 0) return classBlock.slice(open + 1, i);
        }
    }
    return '';
}

/** JS: static fields, get/set, then methods (constructor first among methods). */
function jsMembers(body) {
    const out = [];
    const lines = body.split('\n');
    for (const line of lines) {
        const t = line.trim();
        if (/^static\s+(\w+)\s*=/.test(t)) {
            const m = t.match(/^static\s+(\w+)\s*=/);
            if (m) out.push(`static:${m[1]}`);
        } else if (/^(?:async\s+)?constructor\s*\(/.test(t)) {
            out.push('constructor');
        } else if (/^get\s+(\w+)\s*\(/.test(t)) {
            const m = t.match(/^get\s+(\w+)\s*\(/);
            if (m) out.push(`get:${m[1]}`);
        } else if (/^set\s+(\w+)\s*\(/.test(t)) {
            const m = t.match(/^set\s+(\w+)\s*\(/);
            if (m) out.push(`set:${m[1]}`);
        } else if (/^(\w+)\s*\([^)]*\)\s*\{/.test(t) && !/^\s*(if|for|while|switch|catch)\s*\(/.test(t)) {
            const m = t.match(/^(\w+)\s*\(/);
            if (
                m &&
                !['if', 'for', 'while', 'switch', 'catch', 'function', 'return', 'throw'].includes(m[1])
            ) {
                out.push(`method:${m[1]}`);
            }
        }
    }
    return dedupePreserveOrder(out);
}

function dedupePreserveOrder(arr) {
    const seen = new Set();
    const o = [];
    for (const x of arr) {
        if (!seen.has(x)) {
            seen.add(x);
            o.push(x);
        }
    }
    return o;
}

/**
 * PHP member tokens in **source order** (not `[statics, getters, methods]`, which mis-orders
 * `__construct` before `__get` cases in classes like `LeanUnary`).
 */
function phpMembersOrdered(body, className = null) {
    const out = [];
    const seen = new Set();
    const push = (tok) => {
        if (!seen.has(tok)) {
            seen.add(tok);
            out.push(tok);
        }
    };
    const lines = body.split('\n');
    let inGet = false;
    let getDepth = 0;
    for (let li = 0; li < lines.length; li++) {
        const line = lines[li];
        const t = line.trim();
        if (!inGet && /^public\s+function\s+__get\s*\(/.test(t)) {
            inGet = true;
            getDepth = (line.match(/\{/g) || []).length - (line.match(/\}/g) || []).length;
            continue;
        }
        if (inGet) {
            const caseM = t.match(/^case\s+['"](\w+)['"]\s*:/);
            if (caseM) push(`get:${caseM[1]}`);
            getDepth += (line.match(/\{/g) || []).length - (line.match(/\}/g) || []).length;
            if (getDepth <= 0) inGet = false;
            continue;
        }
        if (/^public\s+static\s+\$(\w+)/.test(t)) {
            const m = t.match(/^public\s+static\s+\$(\w+)/);
            if (m) push(`static:${m[1]}`);
        } else if (/^public\s+function\s+(__construct|__set|__clone)\s*\(/.test(t)) {
            const m = t.match(/^public\s+function\s+(__construct|__set|__clone)\s*\(/);
            if (m[1] === '__construct') push('constructor');
            else if (m[1] === '__set' && className === 'LeanUnary') push('set:arg');
            else push(`magic:${m[1]}`);
        } else if (/^public\s+function\s+(\w+)\s*\(/.test(t)) {
            const m = t.match(/^public\s+function\s+(\w+)\s*\(/);
            if (m && !['__get'].includes(m[1])) {
                const method = m[1] === '__toString' ? 'toString' : m[1];
                push(`method:${method}`);
            }
        }
    }
    return out;
}

/** When PHP omits `public static $input_priority` but JS declares it (runtime parity), drop for compare. */
function alignStaticInputPriority(pMem, jMem, phpInner) {
    const phpDeclaresStatic = /public\s+static\s+\$input_priority/.test(phpInner);
    let p = [...pMem];
    let j = [...jMem];
    if (!phpDeclaresStatic) {
        j = j.filter((x) => x !== 'static:input_priority');
    }
    return [p, j];
}

/** PHP may inherit `command` from `parent::__get`; JS often spells it as `get command()` for `latexFormat`. */
function alignCommandGetter(pMem, jMem) {
    if (!pMem.includes('get:command')) {
        return [pMem, jMem.filter((x) => x !== 'get:command')];
    }
    return [pMem, jMem];
}

const argv = process.argv.slice(2);
const strict = argv.includes('--strict');
const arithmetic = argv.includes('--arithmetic');
const classArg = argv.find((a) => a.startsWith('--class='))?.slice('--class='.length) ||
    (argv.includes('--class') ? argv[argv.indexOf('--class') + 1] : null);

const phpClasses = collectClassOrder(phpClassDecl, phpSrc);
const jsClasses = collectClassOrder(jsClassDecl, jsSrc);
const shared = phpClasses.filter((c) => jsClasses.includes(c));
const arithmeticShared = collectArithmeticOrder(phpSrc).filter((c) => jsClasses.includes(c));

let todo;
if (classArg) {
    const pool = arithmetic ? arithmeticShared : shared;
    todo = pool.filter((c) => c === classArg);
} else if (arithmetic) {
    todo = arithmeticShared;
} else {
    todo = shared;
}

let failed = false;
for (const name of todo) {
    const phpBlock = extractClassBlock(phpSrc, name, false);
    const jsBlock = extractClassBlock(jsSrc, name, true);
    if (!phpBlock || !jsBlock) continue;
    const pInner = innerBody(phpBlock);
    const jInner = innerBody(jsBlock);
    let pMem = phpMembersOrdered(pInner, name);
    let jMem = jsMembers(jInner);
    if (arithmetic) {
        [pMem, jMem] = alignStaticInputPriority(pMem, jMem, pInner);
        [pMem, jMem] = alignCommandGetter(pMem, jMem);
    }
    if (pMem.join('\n') !== jMem.join('\n')) {
        console.error(`\n=== ${name} ===`);
        console.error('PHP:', pMem.join(', ') || '(empty)');
        console.error('JS: ', jMem.join(', ') || '(empty)');
        failed = true;
    }
}

if (failed) {
    console.error(
        '\nError: member lists differ for one or more classes. Align lean.js with lean.php (Step 3).',
    );
    if (strict) process.exit(1);
} else {
    const n = arithmetic ? arithmeticShared.length : shared.length;
    console.log(
        classArg
            ? `OK: ${classArg} member order matches (normalized).`
            : `OK: all ${todo.length} classes in scope match (normalized; total shared ${n}).`,
    );
}

process.exit(strict && failed ? 1 : 0);
