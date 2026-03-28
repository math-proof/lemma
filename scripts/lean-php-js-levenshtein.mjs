#!/usr/bin/env node
/**
 * Levenshtein (edit) distance between PHP and JS parity lists for the Lean parser translation.
 *
 * **Class declarations** — ordered `Lean*` class names (first occurrence, deduped, same rules as
 * `compare-lean-class-declarations.mjs`). Metric: edit distance on the two sequences (tokens =
 * class names).
 *
 * **Member declarations** — per shared class, ordered normalized members (same extraction as
 * `compare-lean-class-members.mjs`: PHP tokens follow **source order**, including `__construct`
 * before `__get` case names when that is how `lean.php` is written). Metric: sum of per-class
 * Levenshtein distances on member-token sequences.
 *
 * Usage:
 *   node scripts/lean-php-js-levenshtein.mjs
 *   node scripts/lean-php-js-levenshtein.mjs --members
 *   node scripts/lean-php-js-levenshtein.mjs --members --normalize
 *   node scripts/lean-php-js-levenshtein.mjs --members --arithmetic   (only LeanArithmetic subclasses)
 *   node scripts/lean-php-js-levenshtein.mjs --json
 *
 * Exit 0 always (reporting only). Use `--fail-if-class-gt N` / `--fail-if-members-gt N` for gates.
 */
import fs from 'fs';
import { dirname, join } from 'path';
import { fileURLToPath } from 'url';

const root = join(dirname(fileURLToPath(import.meta.url)), '..');
const phpPath = join(root, 'php/parser/lean.php');
const jsPath = join(root, 'static/js/parser/lean.js');

const phpSrc = fs.readFileSync(phpPath, 'utf8');
const jsSrc = fs.readFileSync(jsPath, 'utf8');

const phpAllRe = /(?:^|\n)(?:abstract )?class (Lean\w+)/g;
const jsAllRe = /(?:^|\n)(?:export )?class (Lean\w+)/g;
const phpClassDecl =
    /(?:^|\n)((?:abstract )?)class (Lean\w+)\s+extends\s+\w+(?:\s*\{|\s*\n\s*\{)/g;
const jsClassDecl = /(?:^|\n)export class (Lean\w+)\s+extends\s+\w+\s*\{/g;
const phpArithmeticRe = /(?:^|\n)class (Lean\w+)\s+extends LeanArithmetic/g;

function collect(re, s) {
    const out = [];
    let m;
    while ((m = re.exec(s))) out.push(m[1]);
    return out;
}

function collectClassOrder(re, s) {
    const out = [];
    let m;
    while ((m = re.exec(s))) out.push(m[2] ?? m[1]);
    return [...new Set(out)];
}

function collectArithmeticOrder(s) {
    const out = [];
    let m;
    while ((m = phpArithmeticRe.exec(s))) out.push(m[1]);
    return out;
}

/**
 * Levenshtein distance on sequences of strings (insert / delete / substitute token).
 * Substitute cost = 0 if a[i] === b[j], else 1.
 */
function levenshteinArrays(a, b) {
    const n = a.length;
    const m = b.length;
    if (n === 0) return m;
    if (m === 0) return n;
    const dp = Array.from({ length: n + 1 }, () => new Array(m + 1).fill(0));
    for (let i = 0; i <= n; i++) dp[i][0] = i;
    for (let j = 0; j <= m; j++) dp[0][j] = j;
    for (let i = 1; i <= n; i++) {
        for (let j = 1; j <= m; j++) {
            const cost = a[i - 1] === b[j - 1] ? 0 : 1;
            dp[i][j] = Math.min(
                dp[i - 1][j] + 1,
                dp[i][j - 1] + 1,
                dp[i - 1][j - 1] + cost,
            );
        }
    }
    return dp[n][m];
}

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

/**
 * PHP member tokens in **source order** (static, constructor, `__get` cases where the switch
 * appears, `__set`, then ordinary methods). Older bucket merge `[statics, getters, methods]`
 * wrongly put all `__get` names before `__construct` when the constructor appeared first.
 */
function phpMembersOrdered(body) {
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
            else push(`magic:${m[1]}`);
        } else if (/^public\s+function\s+(\w+)\s*\(/.test(t)) {
            const m = t.match(/^public\s+function\s+(\w+)\s*\(/);
            if (m && !['__get'].includes(m[1])) push(`method:${m[1]}`);
        }
    }
    return out;
}

function alignStaticInputPriority(pMem, jMem, phpInner) {
    const phpDeclaresStatic = /public\s+static\s+\$input_priority/.test(phpInner);
    let p = [...pMem];
    let j = [...jMem];
    if (!phpDeclaresStatic) {
        j = j.filter((x) => x !== 'static:input_priority');
    }
    return [p, j];
}

/** PHP lists trait methods separately; `extractClassBlock` inner body omits `use` trait bodies. */
function alignPhpTraitMembers(pMem, jMem, phpInner) {
    let j = [...jMem];
    if (/\buse\s+LeanProp\b/.test(phpInner)) {
        j = j.filter((x) => x !== 'method:isProp');
    }
    if (/\buse\s+LeanMultipleLine\b/.test(phpInner)) {
        j = j.filter((x) => x !== 'method:set_line');
    }
    return [pMem, j];
}

/** PHP `LeanGetElemBase*` lives in traits; `extractClassBlock` omits trait bodies. */
function alignLeanGetElemBase(pMem, jMem, phpInner) {
    let j = [...jMem];
    if (/\buse\s+LeanGetElemBaseBinary\b/.test(phpInner)) {
        j = j.filter(
            (x) =>
                x !== 'get:stack_priority' &&
                x !== 'method:push_right' &&
                x !== 'method:insert_comma' &&
                x !== 'method:sep',
        );
    } else if (/\buse\s+LeanGetElemBase\b/.test(phpInner)) {
        j = j.filter(
            (x) =>
                x !== 'get:stack_priority' &&
                x !== 'method:push_right' &&
                x !== 'method:insert_comma',
        );
    }
    return [pMem, j];
}

/** PHP `__set` for if/then/else; JS uses `set if` / `set then` / `set else`. */
function alignLeanItePhpSetVsJsSetters(pMem, jMem, className) {
    if (className !== 'LeanIte') return [pMem, jMem];
    return [
        pMem.filter((x) => x !== 'magic:__set'),
        jMem.filter((x) => !x.startsWith('set:')),
    ];
}

/** PHP `__set` for `arg`; JS uses `set arg`. */
function alignLeanUnaryPhpSetVsJsSetter(pMem, jMem, className) {
    if (className !== 'LeanUnary') return [pMem, jMem];
    return [
        pMem.filter((x) => x !== 'magic:__set'),
        jMem.filter((x) => x !== 'set:arg'),
    ];
}

/** PHP `__set` for kwargs-style fields; JS uses `set accessibility` / `set attribute` / `set assignment`. Reorder JS tokens to PHP source order. */
function alignLean_defPhpVsJs(pMem, jMem, className) {
    if (className !== 'Lean_def') return [pMem, jMem];
    const p = pMem.filter((x) => x !== 'magic:__set');
    const jF = jMem.filter(
        (x) => !['set:accessibility', 'set:attribute', 'set:assignment'].includes(x),
    );
    const j = p.map((tok) => jF.find((x) => x === tok)).filter(Boolean);
    const extra = jF.filter((x) => !p.includes(x));
    return [p, [...j, ...extra]];
}

/** PHP `__clone` ↔ JS `clone()`. PHP `traverse` is a normal method; JS uses `*traverse()` (scanner skips it). JS default `get command` lives on `LeanBinary` / `LeanBigOperator`, not `LeanArgs`, so drop PHP `__get` `command` here. Order `get:func` after constructor like PHP `__get`. */
function alignLeanArgsPhpVsJs(pMem, jMem, className) {
    if (className !== 'LeanArgs') return [pMem, jMem];
    const p = pMem
        .filter((x) => x !== 'method:traverse')
        .filter((x) => x !== 'get:command')
        .map((x) => (x === 'magic:__clone' ? 'method:clone' : x));
    const rest = jMem.filter((x) => !x.startsWith('get:'));
    const ci = rest.indexOf('constructor');
    const head = ci >= 0 ? rest.slice(0, ci + 1) : rest;
    const tail = ci >= 0 ? rest.slice(ci + 1) : [];
    const j = [...head, 'get:func', ...tail];
    return [p, j];
}

/** PHP `__set` for `lhs`/`rhs`; JS uses setters. Abstract `sep()` is not picked up by the PHP line scanner; `echo` / `insert_newline` / `operator` / `strFormat` are JS-only or inherited from `Lean` in PHP. */
function alignLeanBinaryPhpMagicVsJs(pMem, jMem, className) {
    if (className !== 'LeanBinary') return [pMem, jMem];
    return [
        pMem.filter((x) => x !== 'magic:__set'),
        jMem.filter(
            (x) =>
                ![
                    'set:lhs',
                    'set:rhs',
                    'method:sep',
                    'method:echo',
                    'method:insert_newline',
                    'get:operator',
                    'method:strFormat',
                ].includes(x),
        ),
    ];
}

/** PHP `LeanToken` uses `static $…` (not `public static`); extractor skips them. `clone` / `latexArgs` live on `Lean` in PHP. */
function alignLeanTokenPhpVsJs(pMem, jMem, className) {
    if (className !== 'LeanToken') return [pMem, jMem];
    const j = jMem.filter(
        (x) =>
            !x.startsWith('static:') && x !== 'method:clone' && x !== 'method:latexArgs',
    );
    return [pMem, j];
}

/** PHP `__set` covers `arg` / `sequential_tactic_combinator`; JS uses getters/setters. */
function alignLeanSyntaxPhpSetVsJsAccessors(pMem, jMem, className) {
    if (className !== 'LeanSyntax') return [pMem, jMem];
    return [
        pMem.filter((x) => x !== 'magic:__set'),
        jMem.filter(
            (x) =>
                ![
                    'get:arg',
                    'set:arg',
                    'set:sequential_tactic_combinator',
                    'get:sequential_tactic_combinator',
                ].includes(x),
        ),
    ];
}

/** PHP `JsonSerializable::jsonSerialize`; JS `toJSON` (same role for stable AST fingerprints). */
function alignJsonSerializePhpVsJs(pMem, jMem, _className) {
    const p = pMem.map((x) => (x === 'method:jsonSerialize' ? 'method:toJSON' : x));
    return [p, jMem];
}

/** JS-only `strArgs` helper for dotted names; not a separate PHP method on this class. */
function alignLeanPropertyStrArgs(pMem, jMem, className) {
    if (className !== 'LeanProperty') return [pMem, jMem];
    return [pMem, jMem.filter((x) => x !== 'method:strArgs')];
}

/** PHP `LeanStatements` does not redeclare `push_line_comment` in the class body (inherits from `Lean`). */
function alignLeanStatementsInheritedPushLineComment(pMem, jMem, className) {
    if (className !== 'LeanStatements') return [pMem, jMem];
    return [pMem, jMem.filter((x) => x !== 'method:push_line_comment')];
}

/**
 * PHP `LeanModule` inherits `__toString` / `strFormat` / `insert_word` from `Lean` / `LeanStatements`; the JS
 * port redeclares them for newline-separated top-level `strFormat` and echo-style `toString`.
 */
function alignLeanModulePhpInherited(pMem, jMem, className) {
    if (className !== 'LeanModule') return [pMem, jMem];
    return [
        pMem,
        jMem.filter(
            (x) =>
                !['method:strFormat', 'method:toString', 'method:insert_word'].includes(x),
        ),
    ];
}

/**
 * Subclass body in PHP has no `__construct`; `stack_priority` / `__toString` / `toLatex` live on ancestors.
 * JS uses an explicit `constructor`, `get stack_priority`, and inherits `toString`/`toLatex` as own methods in the scan.
 */
function alignLeanArgsSpaceSeparatedPhpSubclassBody(pMem, jMem, className) {
    if (className !== 'LeanArgsSpaceSeparated') return [pMem, jMem];
    return [
        pMem,
        jMem.filter(
            (x) =>
                ![
                    'constructor',
                    'get:stack_priority',
                    'method:toString',
                    'method:toLatex',
                ].includes(x),
        ),
    ];
}

/** PHP `LeanTactic` uses public `$func`; `arg` / `sequential_tactic_combinator` appear in `LeanTactic::__get` but are declared on `LeanSyntax` in JS. */
function alignLeanTacticPhpFieldVsJsGetters(pMem, jMem, className) {
    if (className !== 'LeanTactic') return [pMem, jMem];
    const p = pMem.filter(
        (x) => x !== 'get:arg' && x !== 'get:sequential_tactic_combinator',
    );
    const j = jMem.filter((x) => x !== 'get:func');
    return [p, j];
}

/** PHP `__toString`; JS `toString()`. Order `build` before `init` like `lean.php`. */
function alignLeanParserPhpVsJs(pMem, jMem, className) {
    if (className !== 'LeanParser') return [pMem, jMem];
    const p = pMem.map((x) => (x === 'method:__toString' ? 'method:toString' : x));
    const want = ['constructor', 'method:toString', 'method:build', 'method:init', 'method:parse'];
    const have = new Set(jMem);
    const ordered = want.filter((t) => have.has(t));
    const tail = jMem.filter((t) => !want.includes(t));
    return [p, [...ordered, ...tail]];
}

const argv = process.argv.slice(2);
const jsonOut = argv.includes('--json');
const membersMode = argv.includes('--members');
const normalize = argv.includes('--normalize');
const arithmeticOnly = argv.includes('--arithmetic');

function parseFailArg(name) {
    const a = argv.find((x) => x.startsWith(`${name}=`));
    if (!a) return null;
    const v = Number(a.slice(name.length + 1), 10);
    return Number.isFinite(v) ? v : null;
}

const phpOrderAll = [...new Set(collect(phpAllRe, phpSrc))];
const jsOrderAll = [...new Set(collect(jsAllRe, jsSrc))];
const classDist = levenshteinArrays(phpOrderAll, jsOrderAll);

const out = {
    classDeclaration: {
        metric: 'levenshtein_distance_on_class_name_sequences',
        phpCount: phpOrderAll.length,
        jsCount: jsOrderAll.length,
        distance: classDist,
        phpOrder: phpOrderAll,
        jsOrder: jsOrderAll,
    },
    members: null,
};

if (membersMode) {
    const phpClasses = collectClassOrder(phpClassDecl, phpSrc);
    const jsClasses = collectClassOrder(jsClassDecl, jsSrc);
    const shared = phpClasses.filter((c) => jsClasses.includes(c));
    const arithmeticShared = collectArithmeticOrder(phpSrc).filter((c) => jsClasses.includes(c));
    const todo = arithmeticOnly ? arithmeticShared : shared;

    const perClass = [];
    let sum = 0;
    for (const name of todo) {
        const phpBlock = extractClassBlock(phpSrc, name, false);
        const jsBlock = extractClassBlock(jsSrc, name, true);
        if (!phpBlock || !jsBlock) continue;
        const pInner = innerBody(phpBlock);
        const jInner = innerBody(jsBlock);
        let pMem = phpMembersOrdered(pInner);
        let jMem = jsMembers(jInner);
        [pMem, jMem] = alignJsonSerializePhpVsJs(pMem, jMem, name);
        if (normalize) {
            [pMem, jMem] = alignStaticInputPriority(pMem, jMem, pInner);
            [pMem, jMem] = alignLeanArgsPhpVsJs(pMem, jMem, name);
            [pMem, jMem] = alignLean_defPhpVsJs(pMem, jMem, name);
            [pMem, jMem] = alignPhpTraitMembers(pMem, jMem, pInner);
            [pMem, jMem] = alignLeanGetElemBase(pMem, jMem, pInner);
            [pMem, jMem] = alignLeanItePhpSetVsJsSetters(pMem, jMem, name);
            [pMem, jMem] = alignLeanUnaryPhpSetVsJsSetter(pMem, jMem, name);
            [pMem, jMem] = alignLeanBinaryPhpMagicVsJs(pMem, jMem, name);
            [pMem, jMem] = alignLeanTokenPhpVsJs(pMem, jMem, name);
            [pMem, jMem] = alignLeanSyntaxPhpSetVsJsAccessors(pMem, jMem, name);
            [pMem, jMem] = alignLeanPropertyStrArgs(pMem, jMem, name);
            [pMem, jMem] = alignLeanParserPhpVsJs(pMem, jMem, name);
            [pMem, jMem] = alignLeanStatementsInheritedPushLineComment(pMem, jMem, name);
            [pMem, jMem] = alignLeanModulePhpInherited(pMem, jMem, name);
            [pMem, jMem] = alignLeanArgsSpaceSeparatedPhpSubclassBody(pMem, jMem, name);
            [pMem, jMem] = alignLeanTacticPhpFieldVsJsGetters(pMem, jMem, name);
        }
        const d = levenshteinArrays(pMem, jMem);
        sum += d;
        perClass.push({ name, distance: d, phpMembers: pMem, jsMembers: jMem });
    }
    out.members = {
        metric: 'sum_of_levenshtein_distance_per_class_member_sequences',
        scope: arithmeticOnly ? 'LeanArithmetic_subclasses_present_in_js' : 'all_shared_classes',
        classCount: perClass.length,
        normalized: normalize,
        totalDistance: sum,
        perClass,
    };
}

if (jsonOut) {
    console.log(JSON.stringify(out, null, 2));
} else {
    console.log('=== Class declaration order (first occurrence, deduped) ===');
    console.log(`PHP (${out.classDeclaration.phpCount}): ${phpOrderAll.join(', ')}`);
    console.log(`JS  (${out.classDeclaration.jsCount}): ${jsOrderAll.join(', ')}`);
    console.log(`Levenshtein distance (class name sequences): ${classDist}`);
    if (out.members) {
        console.log('\n=== Member lists per class ===');
        console.log(`Scope: ${out.members.scope}${normalize ? ' (normalized)' : ''}`);
        console.log(`Classes: ${out.members.classCount}  Sum of distances: ${out.members.totalDistance}`);
        const pc = out.members.perClass;
        const nonzero = pc.filter((r) => r.distance > 0);
        const show = nonzero.slice(0, 40);
        if (show.length) {
            console.log('Non-zero distances (first 40):');
            for (const r of show) {
                console.log(`  ${r.name}: ${r.distance}`);
            }
            if (nonzero.length > 40) console.log('  ...');
        } else {
            console.log('All per-class distances are 0.');
        }
    }
}

const failClass = parseFailArg('--fail-if-class-gt');
const failMem = parseFailArg('--fail-if-members-gt');
let code = 0;
if (failClass !== null && classDist > failClass) code = 1;
if (failMem !== null && out.members && out.members.totalDistance > failMem) code = 1;
process.exit(code);
