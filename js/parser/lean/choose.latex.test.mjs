/**
 * `((i : ℕ).choose j : ℝ)` with `i : Fin _` → `\binom{i}{j}`, not `\binom{i : ℕ}{j}`.
 * Run: `node js/parser/lean/choose.latex.test.mjs`
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

{
  const src = `
lemma main
  {n : ℕ} {i j : Fin n} {d h : ℕ}
-- given
  (h : True) :
-- imply
  ((i : ℕ).choose j : ℝ) * (d.choose h : ℝ) = (Nat.choose (i : ℕ) j : ℝ) := by
  sorry
`;
  const latex = compile(src).render2vue(false).lemma[0].imply?.latex ?? '';
  check('no i : ℕ inside binom', !/\\binom\{\{i\} : \{ℕ\}\}/.test(latex) && !latex.includes('\\binom{{i} : {ℕ}}'), latex);
  check('has \\binom{i}{j} (or {i}/{j})', /\\binom\{.?i.?\}\{.?j.?\}/.test(latex) || latex.includes('\\binom{i}{j}'), latex);
  check('plain d.choose h still binom', latex.includes('\\binom{d}{h}'), latex);
  check('Nat.choose (i : ℕ) j also peels', !/\\binom\{\{i\} :/.test(latex), latex);
  console.log('SAMPLE:', latex);
}

{
  const f = 'Lemma/Matrix/DetOf/eq/PowSub__Mul.lean';
  const latex = compile(fs.readFileSync(f, 'utf8')).render2vue(false).lemma[0].imply?.latex ?? '';
  check('PowSub__Mul: no (i : ℕ) in binom', !/\\binom\{[^}]*: [^}]*ℕ/.test(latex), latex.slice(0, 400));
  check('PowSub__Mul: has binom with i', /\\binom\{[^}]*i/.test(latex), latex.slice(0, 300));
}

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
