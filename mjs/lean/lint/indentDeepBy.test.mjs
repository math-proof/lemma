/**
 * `indent-deep` after `:= by`: tactic body must be +2, not +4.
 * Run: `node mjs/lean/lint/indentDeepBy.test.mjs`
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
    '      _ = True := by',
    '          rw [h]',
    '          trivial',
    '  trivial',
].join('\n'));

const GOOD = lemma([
    '  have : True := by',
    '    calc',
    '      _ = True := by',
    '        rw [h]',
    '        trivial',
    '  trivial',
].join('\n'));

let failed = 0;
function check(name, cond, detail = '') {
    if (!cond) {
        failed++;
        console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
    } else console.log(`ok   ${name}`);
}

function deepWarns(src) {
    return lintLean(src, { file: 'Lemma/Dummy/Test.lean', rules: ['indent-deep'], ast: false })
        .filter((w) => w.rule === 'indent-deep');
}

{
    const w = deepWarns(BAD);
    check('+4 after `:= by` warns indent-deep', w.length >= 1, `got ${w.length}: ${w.map((x) => x.info).join('; ')}`);
    check('message says indent by 2', /indent by 2/.test(w[0]?.info || ''), w[0]?.info);
    check('AGENTS.md 2-indented quote', /strictly 2-indented/.test(w[0]?.info || ''), w[0]?.info);
    check('points at over-indented tactic', /rw/.test(w[0]?.code || ''), `code=${JSON.stringify(w[0]?.code)}`);
}

{
    const w = deepWarns(GOOD);
    check('+2 after `:= by` quiet', w.length === 0, w.map((x) => x.info).join('; '));
}

{
    // term continuation after `:=` (no `by`) may still go deeper without indent-deep
    const src = lemma([
        '  have : True :=',
        '      trivial',
        '  trivial',
    ].join('\n'));
    const w = deepWarns(src);
    check('`:=` term continuation still exempt', w.length === 0, w.map((x) => x.info).join('; '));
}

if (failed) {
    console.error(`${failed} failed`);
    process.exit(1);
}

console.log('--- before/after ---');
for (const [label, src] of [['BEFORE', BAD], ['AFTER', GOOD]]) {
    const all = deepWarns(src);
    console.log(label + ':');
    if (!all.length) console.log('  (no indent-deep warnings)');
    for (const x of all) console.log(`  warning:${x.line}:${x.col ?? '?'}: ${x.info}`);
}
console.log('all passed');
