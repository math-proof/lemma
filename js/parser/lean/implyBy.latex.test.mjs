/**
 * `-- imply` LaTeX keeps the `:= by` that closes the statement.
 * Run: `node js/parser/lean/implyBy.latex.test.mjs`
 */
import { compile } from '../lean.js';
import fs from 'fs';

let failed = 0;
function check(name, cond, detail = '') {
  if (!cond) {
    failed++;
    console.error(`FAIL ${name}${detail ? ': ' + detail : ''}`);
  } else {
    console.log(`ok   ${name}`);
  }
}

const tagSuffix = '\\tag*{ := {\\color{#00f}by}}';

{
  const lx = compile('lemma m : True := by sorry').render2vue(false).lemma[0].imply.latex;
  check('one-line := by', lx.endsWith(tagSuffix), lx);
}

{
  const p = 'Lemma/Complex/Any_All_Eq_Dot_MulDescFactorial/of/All_Eq_Dot.lean';
  const lem = compile(fs.readFileSync(p, 'utf8')).render2vue(false).lemma.find((l) => l.name === 'main');
  check('main lean keeps := by', lem.imply.lean.trimEnd().endsWith(':= by'), lem.imply.lean.slice(-40));
  check('main latex ends := by tag*', lem.imply.latex.endsWith(tagSuffix), lem.imply.latex.slice(-80));
}

{
  const lx = compile('lemma m : True := trivial').render2vue(false).lemma[0].imply.latex;
  check('term proof has no by', !lx.includes('\\color{#00f}by'), lx);
}

{
  // Wide Cholesky-style imply: still right-margin \tag* (Body priority).
  const p = 'Lemma/Matrix/Any_And_Eq_Mul_Adjoint/of/All_Lt0Dot_MulVec/EqAdjoint.lean';
  const lem = compile(fs.readFileSync(p, 'utf8')).render2vue(false).lemma.find((l) => l.name === 'main');
  const lx = lem.imply.latex;
  check('wide imply uses tag* := by', lx.endsWith(tagSuffix), lx.slice(-80));
  check('wide imply has no quad :=', !lx.includes('\\quad :='), lx.slice(-80));
  check('wide imply keeps magenta dagger', lx.includes('{\\dagger}'), lx.slice(-120));
}

if (failed) process.exit(1);
console.log('all ok');
