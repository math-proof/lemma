/**
 * Term `let` body on the next line must not glue onto the value
 * (`4 * a * c` then `x ∈` rendered as 4acx).
 * Run: `node js/parser/lean/letBody.latex.test.mjs`
 */
import { compile } from '../lean.js';
import fs from 'fs';

const src = fs.readFileSync(
  'Lemma/Complex/Eq0Add_Mul_Square/is/In_FinsetDivS_Mul2/of/Ne_0.lean',
  'utf8',
);
const latex = compile(src).render2vue(false).lemma[0].imply.latex;
const ok = /\{4\s+a\s+c\}.*\\\\&\{x\}/.test(latex);
if (!ok) {
  console.error('FAIL let body glued onto 4*a*c:\n', latex);
  process.exit(1);
}
console.log('ok   let body is a new aligned row');
