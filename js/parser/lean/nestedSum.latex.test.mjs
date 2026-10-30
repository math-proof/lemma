/**
 * Nested Finset ∑ ∑ → one ∑ with stacked limits (display-only).
 * Run: `node js/parser/lean/nestedSum.latex.test.mjs`
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

const nested = implyLatex(
  `lemma t {m n : ℕ} {x : ℕ → ℕ → ℝ} : ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, x i j = 0 := by sorry`,
);
check('nested range: one sum', (nested.match(/\\sum\\limits_/g) || []).length === 1, nested);
check('nested range: stacked limits', /\\sum\\limits_\{\\substack\{j < n \\\\ i < m\}\}/.test(nested), nested);
check('nested range: no adjacent sums', !/\\sum\\limits_\{i < m\} \{\\sum/.test(nested), nested);

const triple = implyLatex(
  `lemma t {a b c : ℕ} {x : ℕ → ℕ → ℕ → ℝ} : ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, ∑ k ∈ Finset.range c, x i j k = 0 := by sorry`,
);
check('triple: one sum', (triple.match(/\\sum\\limits_/g) || []).length === 1, triple);
check('triple: three stacked binders', /k < c \\\\ j < b \\\\ i < a/.test(triple), triple);

const paren = implyLatex(
  `lemma t {m n : ℕ} {x : ℕ → ℕ → ℝ} : ∑ i ∈ Finset.range m, (∑ j ∈ Finset.range n, x i j) = 0 := by sorry`,
);
check('paren inner still stacks', /\\substack\{j < n \\\\ i < m\}/.test(paren), paren);

const single = implyLatex(
  `lemma t {n : ℕ} {f : ℕ → ℝ} : ∑ i ∈ Finset.range n, f i = 0 := by sorry`,
);
check('single unchanged', /\\sum\\limits_\{i < n\}/.test(single), single);
check('single not substack', !/substack/.test(single), single);

const mixedClosed = implyLatex(
  `lemma t {d n : ℕ} {f : ℕ → ℕ → ℝ} : ∑ h ∈ Finset.range (d + 1), ∑ j ∈ Finset.range n, f h j = 0 := by sorry`,
);
check('closed+plain stacks with inequality', /j < n \\\\ 0 \\le h \\le d/.test(mixedClosed), mixedClosed);
check('closed+plain one sum', (mixedClosed.match(/\\sum\\limits_/g) || []).length === 1, mixedClosed);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
