/**
 * `proof-blank-line`: no empty lines inside the proof body.
 * Run: `node mjs/lean/lint/proofBlankLine.test.mjs`
 */
import { lintLean } from './index.mjs';

function lemma(proofBody, trailing = '\n\n-- created on 2026-10-10\n') {
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
        trailing,
    ].join('\n');
}

const BAD = lemma([
    '  have : True := by',
    '    trivial',
    '',
    '  -- next step',
    '  trivial',
].join('\n'));

const GOOD = lemma([
    '  have : True := by',
    '    trivial',
    '  -- next step',
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
    return lintLean(src, { file: 'Lemma/Dummy/Test.lean', rules: ['proof-blank-line'], ast: false })
        .filter((w) => w.rule === 'proof-blank-line');
}

{
    const w = warns(BAD);
    check('blank between proof steps warns', w.length === 1, `got ${w.length}: ${w.map((x) => x.info).join('; ')}`);
    check('message mentions blank line inside the proof', /blank line inside the proof/.test(w[0]?.info || ''), w[0]?.info);
    check('no AGENTS.md quote (lint-only)', !/AGENTS\.md:/.test(w[0]?.info || ''), w[0]?.info);
}

{
    const w = warns(GOOD);
    check('contiguous proof quiet', w.length === 0, w.map((x) => x.info).join('; '));
}

{
    // two blanks before `-- created on` must not warn (date-spacing)
    const src = lemma('  trivial', '\n\n\n-- created on 2026-10-10\n');
    const w = warns(src);
    check('blanks before date footer quiet', w.length === 0, w.map((x) => x.info).join('; '));
}

{
    // header blanks (import then two blanks) are outside the proof
    const w = warns(GOOD);
    check('header two-blank layout unaffected', w.length === 0);
}

if (failed) {
    console.error(`${failed} failed`);
    process.exit(1);
}

console.log('--- before/after ---');
for (const [label, src] of [['BEFORE', BAD], ['AFTER', GOOD]]) {
    const all = warns(src);
    console.log(label + ':');
    if (!all.length) console.log('  (no proof-blank-line warnings)');
    for (const x of all) console.log(`  warning:${x.line}:${x.col ?? '?'}: ${x.info}`);
}
console.log('all passed');
