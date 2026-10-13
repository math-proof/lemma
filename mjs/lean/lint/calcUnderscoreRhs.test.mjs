/**
 * `calc-underscore-rhs`: do not leave `_ =` alone; put the RHS expression on that line.
 * Run: `node mjs/lean/lint/calcUnderscoreRhs.test.mjs`
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

const BAD = lemma([
    '  have : True := by',
    '    calc',
    '      _ =',
    '        True :=',
    '          trivial',
    '      _ =',
    '        True := trivial',
    '  trivial',
].join('\n'));

const GOOD = lemma([
    '  have : True := by',
    '    calc',
    '      _ = True :=',
    '        trivial',
    '      _ = True := trivial',
    '  trivial',
].join('\n'));

let failed = 0;
function check(name, cond, detail = '') {
    if (!cond) {
        failed++;
        console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
    } else console.log(`ok   ${name}`);
}

function warns(src, rule = 'calc-underscore-rhs') {
    return lintLean(src, { file: 'Lemma/Dummy/Test.lean', rules: [rule], ast: false })
        .filter((w) => w.rule === rule);
}

{
    const w = warns(BAD);
    check('lone `_ =` warns', w.length === 2, `got ${w.length}: ${w.map((x) => x.info).join('; ')}`);
    check('message mentions same line as `_ =`', /same line as `_ =`/.test(w[0]?.info || ''), w[0]?.info);
    check('no AGENTS.md quote (lint-only)', !/AGENTS\.md:/.test(w[0]?.info || ''), w[0]?.info);
}

{
    const w = warns(GOOD);
    check('`_ = expr := …` quiet', w.length === 0, w.map((x) => x.info).join('; '));
}

{
    // coexist with align: good align + bad rhs still only rhs when filtered
    const wAlign = warns(BAD, 'calc-underscore-align');
    check('aligned `_` column does not fire align', wAlign.length === 0, wAlign.map((x) => x.info).join('; '));
}

if (failed) {
    console.error(`${failed} failed`);
    process.exit(1);
}

console.log('--- before/after ---');
for (const [label, src] of [['BEFORE', BAD], ['AFTER', GOOD]]) {
    const all = lintLean(src, { file: 'Lemma/Dummy/CalcRhs.lean', rules: ['calc-underscore-rhs'], ast: false });
    console.log(label + ':');
    if (!all.length) console.log('  (no calc-underscore-rhs warnings)');
    for (const x of all) console.log(`  warning:${x.line}:${x.col ?? '?'}: ${x.info}`);
}
console.log('all passed');
