/**
 * `Finset.card {i : Fin n | r i = z}` → `\left| {set} \right|`.
 * Run: `node js/parser/lean/finsetCard.latex.test.mjs`
 */
import { compile } from '../lean.js';

let failed = 0;
function check(name, cond, detail = '') {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

function imply(src) {
  return compile(src).render2vue(false).lemma[0].imply.latex;
}

{
  const lx = imply('lemma m : Finset.card {i : Fin n | r i = z} = 0 := by sorry');
  check('bars', /\\left\|/.test(lx) && /\\right\|/.test(lx), lx);
  check('no Finset word', !/Finset/.test(lx), lx);
  check('set condition stays', /r i = z|r\\ i/.test(lx) || lx.includes('r') && lx.includes('z'), lx);
}

{
  const lx = imply('lemma m : s.card = 0 := by sorry');
  check('s.card keeps bars', /\\left\|/.test(lx) && /\\right\|/.test(lx), lx);
  check('s.card has s', /s/.test(lx), lx);
}

if (failed) process.exit(1);
console.log('all ok');
