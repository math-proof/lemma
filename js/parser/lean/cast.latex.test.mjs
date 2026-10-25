/**
 * Cast elision `(x : T)` → `x` in LaTeX when the target type is obvious:
 * big-operator scope (`∏ j ∈ s, (j ! : ℝ)` → `j !`), application args, relational operands.
 * Parenthesized big-op binders (`∑ (i : Fin n), …`) keep their ascription.
 * Factorial renders with a visible space: `{%s}\ {!}` (KaTeX collapses source whitespace).
 * Run: `node js/parser/lean/cast.latex.test.mjs`
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

function implyLatex(src) {
  return compile(src).render2vue(false).lemma?.[0]?.imply?.latex ?? '';
}

const prodCast = implyLatex(
  `lemma t1 {d : ℕ} : ∏ j ∈ Finset.range d, (j ! : ℝ) = 1 := by sorry`,
);
check('bigop scope cast elided', !prodCast.includes(':') && !prodCast.includes('ℝ'), prodCast);
check('bigop scope cast parens dropped', !/\\left\(/.test(prodCast), prodCast);
check('factorial has visible space', /\{j\}\\ \{!\}/.test(prodCast), prodCast);

const sumCast = implyLatex(
  `lemma t2 {n : ℕ} : ∑ i ∈ Finset.range n, (i : ℝ) ^ 2 = 0 := by sorry`,
);
check('sum scope cast elided', !sumCast.includes('ℝ'), sumCast);

const appCast = implyLatex(
  `lemma t3 {d : ℕ} {f : ℝ → ℝ} : ∏ j ∈ Finset.range d, f (j ! : ℝ) = 1 := by sorry`,
);
check('application arg cast elided', !appCast.includes('ℝ'), appCast);
check('application arg factorial spaced', /\{j\}\\ \{!\}/.test(appCast), appCast);

const binder = implyLatex(
  `lemma t4 {n : ℕ} {f : Fin n → ℝ} : ∑ (i : Fin n), f i = 0 := by sorry`,
);
check('bigop binder ascription kept', binder.includes('Fin') && binder.includes(':'), binder);

const binderToken = implyLatex(
  `lemma t5 {f : ℕ → ℝ} : ∑ (i : ℕ), f i = 0 := by sorry`,
);
check('token-typed binder ascription kept', binderToken.includes('ℕ') && binderToken.includes(':'), binderToken);

const nested = implyLatex(
  `lemma t6 {m n : ℕ} : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, (j ! : ℝ) = 0 := by sorry`,
);
check('nested bigop scope cast elided', !nested.includes('ℝ'), nested);

const projFactorial = implyLatex(
  `lemma t7 {j : ℕ} {f : ℝ → ℝ} : f (j.factorial : ℝ) = 0 := by sorry`,
);
check('j.factorial cast elided with space', !projFactorial.includes('ℝ') && /\{j\}\\ \{!\}/.test(projFactorial), projFactorial);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
