/**
 * `show T from e` must keep a visible space before `e` in KaTeX
 * (`from y[:m]`, not `fromy[:m]`).
 * Run: `node js/parser/lean/from.latex.test.mjs`
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

const src = `
lemma main
  [MeasurableSpace Ω]
  {π : Measure Ω} {x : ℕ → Ω → α} {y : ℕ → Ω → β} {m : ℕ}
-- given
  (hxy : ∀ i, SinglePSpace π (x i, show Ω → Fin m → β from y[:m])) :
-- imply
  True := by
  sorry
`;

const latex = compile(src).render2vue(false).lemma[0].given?.[0]?.latex ?? '';
check('has explicit TeX space after from', /from\}\s*\\s/.test(latex) || latex.includes('from}\\ '), latex);
check('from is keyword-colored', latex.includes('{\\color{#00f}from}'), latex);
check('not bare from{y} glued', !/from\s*\{y\}/.test(latex.replace(/\\color\{#00f\}from/g, 'FROM')), latex);

import fs from 'fs';
const full = fs.readFileSync('Lemma/Random/Eq/ArgMax/Mul/Prod_ProbCond/of/Ne_0/Eq.lean', 'utf8');
const fullLatex = (compile(full).render2vue(false).lemma[0].given ?? [])
  .find((g) => (g.lean ?? '').includes('from y[:m]'))?.latex ?? '';
check(
  'Eq.lean hxy: from}\\  before y',
  fullLatex.includes('from}\\ ') || /from\}\s*\\ /.test(fullLatex),
  fullLatex.slice(0, 350),
);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
console.log('SAMPLE:', latex.slice(0, 280));
