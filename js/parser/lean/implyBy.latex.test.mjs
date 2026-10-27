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

const suffix = '\\tag*{ := {\\color{#00f}by}}';

{
  const lx = compile('lemma m : True := by sorry').render2vue(false).lemma[0].imply.latex;
  check('one-line := by', lx.endsWith(suffix), lx);
}

{
  const p = 'Lemma/Complex/Any_All_Eq_Dot_MulDescFactorial/of/All_Eq_Dot.lean';
  const lem = compile(fs.readFileSync(p, 'utf8')).render2vue(false).lemma.find((l) => l.name === 'main');
  check('main lean keeps := by', lem.imply.lean.trimEnd().endsWith(':= by'), lem.imply.lean.slice(-40));
  check('main latex ends := by', lem.imply.latex.endsWith(suffix), lem.imply.latex.slice(-80));
}

{
  const lx = compile('lemma m : True := trivial').render2vue(false).lemma[0].imply.latex;
  check('term proof has no by', !lx.includes('\\color{#00f}by'), lx);
}

if (failed) process.exit(1);
console.log('all ok');
