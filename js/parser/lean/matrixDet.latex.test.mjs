/**
 * `Matrix.det L` / `L.det` → `\left| L \right|` (bars around the matrix, not `Matrix`).
 * Run: `node js/parser/lean/matrixDet.latex.test.mjs`
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
  const lx = imply('lemma m : Matrix.det L = 0 := by sorry');
  check('Matrix.det L bars', /\\left\|/.test(lx) && /\\right\|/.test(lx), lx);
  check('Matrix.det L no Matrix word', !/Matrix/.test(lx), lx);
  check('Matrix.det L has L', /L/.test(lx), lx);
}

{
  const lx = imply('lemma m : Matrix.det L[k] = 0 := by sorry');
  check('Matrix.det L[k] bars', /\\left\|/.test(lx) && /\\right\|/.test(lx), lx);
  check('Matrix.det L[k] no Matrix word', !/Matrix/.test(lx), lx);
  check('Matrix.det L[k] has L', /L/.test(lx), lx);
}

{
  const lx = imply('lemma m : L.det = 0 := by sorry');
  check('L.det bars', /\\left\|/.test(lx) && /\\right\|/.test(lx), lx);
  check('L.det has L', /L/.test(lx), lx);
}

{
  const lx = imply('lemma m : Finset.card {i : Fin n | r i = z} = 0 := by sorry');
  check('Finset.card still bars', /\\left\|/.test(lx) && /\\right\|/.test(lx), lx);
  check('Finset.card no Finset word', !/Finset/.test(lx), lx);
}

if (failed) process.exit(1);
console.log('all ok');
