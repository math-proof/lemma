/**
 * `given-hyp-index`: numbered `-- given` hyps must start at h₀/h0 with no gaps.
 * Run: `node mjs/lean/lint/givenHypIndex.test.mjs`
 */
import { lintLean } from './index.mjs';

function lemma(givenBody) {
    return [
        'import Lemma.Dummy',
        '',
        '',
        '/-- test -/',
        '@[path]',
        'private lemma main',
        '  {α : Type*}',
        '-- given',
        givenBody,
        '-- imply',
        '  True := by',
        '-- proof',
        '  have h₀ : True := trivial',
        '  trivial',
        '',
        '',
        '-- created on 2026-10-10',
        '',
    ].join('\n');
}

let failed = 0;
function check(name, cond, detail = '') {
    if (!cond) {
        failed++;
        console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
    } else console.log(`ok   ${name}`);
}

function warns(src) {
    return lintLean(src, { file: 'Lemma/Dummy/Test.lean', rules: ['given-hyp-index'], ast: false })
        .filter((w) => w.rule === 'given-hyp-index');
}

{
    const src = lemma('  (h₄ : True)\n  (h₅ : True) :');
    const w = warns(src);
    check('h₄/h₅ without h₀ warns', w.length === 1, `got ${w.length}`);
    check('message mentions skip h₀', /skips `h₀`/.test(w[0]?.info || ''), w[0]?.info);
    check('points at first numbered binder', w[0]?.line === 9, `line=${w[0]?.line}`);
}

{
    const src = lemma('  (h0 : True)\n  (h2 : True) :');
    const w = warns(src);
    check('ASCII h0,h2 gap warns', w.length === 1, `got ${w.length}`);
    check('message mentions missing h1', /missing h1/.test(w[0]?.info || ''), w[0]?.info);
}

{
    const src = lemma('  (hG : True)\n  (hr : True)\n  (h₀ : True)\n  (h₁ : True) :');
    const w = warns(src);
    check('descriptive + contiguous h₀/h₁ quiet', w.length === 0, w.map((x) => x.info).join('; '));
}

{
    const src = lemma('  (hG : True)\n  (hr : True) :');
    const w = warns(src);
    check('only descriptive names quiet', w.length === 0);
}

{
    // proof-local have h₀ must not count; given has only h₄
    const src = lemma('  (h₄ : True) :');
    const w = warns(src);
    check('ignores proof have h₀; still warns on given h₄', w.length === 1 && /skips `h₀`/.test(w[0]?.info || ''), w[0]?.info);
}

{
    const src = lemma('  (h₀ : True)\n  (h₁ : True)\n  (h₃ : True) :');
    const w = warns(src);
    check('gap h₀,h₁,h₃ warns missing h₂', w.length === 1 && /missing h₂/.test(w[0]?.info || ''), w[0]?.info);
}

if (failed) {
    console.error(`${failed} failed`);
    process.exit(1);
}
console.log('all passed');
