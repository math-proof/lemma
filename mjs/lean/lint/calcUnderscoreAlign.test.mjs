/**
 * `calc-underscore-align`: bare `calc`; every step `_` at calc+2 (same column under it).
 * Run: `node mjs/lean/lint/calcUnderscoreAlign.test.mjs`
 */
import { lintLean } from './index.mjs';

function lemma(proofBody) {
    return [
        'import Lemma.Dummy',
        '',
        '',
        '/-- test -/',
        '@[path]',
        'private lemma main',
        '-- given',
        '  (h : True) :',
        '-- imply',
        '  True := by',
        '-- proof',
        proofBody,
        '',
        '',
        '-- created on 2026-10-10',
        '',
    ].join('\n');
}

/** `calc _ =` on one line — first `_` cannot align with body `_`s. */
const BAD_SAME_LINE = lemma([
    '  have : True := by',
    '    calc _ =',
    '      True := trivial',
    '    _ = True := trivial',
    '  trivial',
].join('\n'));

/** Body `_`s not at calc+2. */
const BAD_MISALIGNED = lemma([
    '  have : True := by',
    '    calc',
    '      _ =',
    '        True := trivial',
    '        _ = True := trivial',
    '  trivial',
].join('\n'));

const GOOD = lemma([
    '  have : True := by',
    '    calc',
    '      _ =',
    '        True := trivial',
    '      _ =',
    '        True := trivial',
    '  trivial',
].join('\n'));

let failed = 0;
function check(name, cond, detail = '') {
    if (!cond) {
        failed++;
        console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
    } else console.log(`ok   ${name}`);
}

function warns(src) {
    return lintLean(src, { file: 'Lemma/Dummy/Test.lean', rules: ['calc-underscore-align'], ast: false })
        .filter((w) => w.rule === 'calc-underscore-align');
}

{
    const w = warns(BAD_SAME_LINE);
    check('`calc _ =` on one line warns', w.length >= 1, `got ${w.length}: ${w.map((x) => x.info).join('; ')}`);
    check('message mentions alone on its line', /alone on its line/.test(w[0]?.info || ''), w[0]?.info);
    check('no AGENTS.md quote (lint-only)', !/AGENTS\.md:/.test(w[0]?.info || ''), w[0]?.info);
}

{
    const w = warns(BAD_MISALIGNED);
    check('misaligned body `_ =` warns', w.length === 1, `got ${w.length}: ${w.map((x) => x.info).join('; ')}`);
    check('message mentions under calc column', /under `calc`/.test(w[0]?.info || ''), w[0]?.info);
}

{
    const w = warns(GOOD);
    check('bare `calc` + `_` at +2 quiet', w.length === 0, w.map((x) => x.info).join('; '));
}

{
    const src = lemma([
        '  have : True := by',
        '    calc',
        '      _ =',
        '        True :=',
        '          trivial',
        '      _ =',
        '        True := trivial',
        '  trivial',
    ].join('\n'));
    const w = warns(src);
    check('deep RHS under `_ =` is fine', w.length === 0, w.map((x) => x.info).join('; '));
}

if (failed) {
    console.error(`${failed} failed`);
    process.exit(1);
}

console.log('--- before/after (run.mjs-style) ---');
for (const [label, src] of [['BEFORE', BAD_SAME_LINE], ['AFTER', GOOD]]) {
    const all = lintLean(src, { file: 'Lemma/Dummy/CalcAlign.lean', rules: ['calc-underscore-align'], ast: false });
    console.log(label + ':');
    if (!all.length) console.log('  (no calc-underscore-align warnings)');
    for (const x of all) console.log(`  warning:${x.line}:${x.col ?? '?'}: ${x.info}`);
}
console.log('all passed');
