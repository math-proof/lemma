/**
 * Finset.range (e + 1) → ∑_{i=0}^{e}; plain Finset.range n stays ∑_{i < n}.
 * Finset.Iio k → ∑_{t < k}; Finset.Iic k → ∑_{t ≤ k} (not (−∞,k)).
 * Run: `node js/parser/lean/range.latex.test.mjs`
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

const closed = implyLatex(
  `lemma t1 {d : ℕ} {f : ℕ → ℝ} : ∑ h ∈ Finset.range (d + 1), f h = 0 := by sorry`,
);
check('range (d+1) uses limits 0..d', /\\sum\\limits_\{h=0\}\^\{d\}/.test(closed), closed);
check('range (d+1) not less-than form', !/h < /.test(closed), closed);

const plain = implyLatex(
  `lemma t2 {n : ℕ} {f : ℕ → ℝ} : ∑ h ∈ Finset.range n, f h = 0 := by sorry`,
);
check('plain range n stays < n', /\\sum\\limits_\{h < n\}/.test(plain), plain);
check('plain range n not 0.. form', !/h=0/.test(plain), plain);

const prodClosed = implyLatex(
  `lemma t3 {d : ℕ} {f : ℕ → ℝ} : ∏ h ∈ Finset.range (d + 1), f h = 0 := by sorry`,
);
check('prod range (d+1) uses limits 0..d', /\\prod\\limits_\{h=0\}\^\{d\}/.test(prodClosed), prodClosed);

const bareRange = implyLatex(
  `lemma t4 {d : ℕ} {f : ℕ → ℝ} : ∑ h ∈ range (d + 1), f h = 0 := by sorry`,
);
check('bare range (d+1) uses limits 0..d', /\\sum\\limits_\{h=0\}\^\{d\}/.test(bareRange), bareRange);

const ico = implyLatex(
  `lemma t5 {a b : ℕ} {f : ℕ → ℝ} : ∏ i ∈ Finset.Ico a (b + 1), f i = 0 := by sorry`,
);
check('icoClosedBound still a..b', /\\prod\\limits_\{i=a\}\^\{b\}/.test(ico), ico);


const iio = implyLatex(
  `lemma t6 {k : ℕ} {d : ℕ → ℝ} : ∑ t ∈ Finset.Iio k, d t = 0 := by sorry`,
);
check('Iio uses t < k', /\\sum\\limits_\{t < k\}/.test(iio), iio);
check('Iio not (-\\\\infty', !/-\\\\infty/.test(iio) && !/\\infty/.test(iio), iio);

const iic = implyLatex(
  `lemma t7 {k : ℕ} {d : ℕ → ℝ} : ∑ t ∈ Finset.Iic k, d t = 0 := by sorry`,
);
check('Iic uses t \\le k', /\\sum\\limits_\{t \\le k\}/.test(iic), iic);
check('Iic not (-\\\\infty', !/-\\\\infty/.test(iic) && !/\\infty/.test(iic), iic);

const bareIio = implyLatex(
  `lemma t8 {k : ℕ} {d : ℕ → ℝ} : ∑ t ∈ Iio k, d t = 0 := by sorry`,
);
check('bare Iio uses t < k', /\\sum\\limits_\{t < k\}/.test(bareIio), bareIio);

const prodIic = implyLatex(
  `lemma t9 {k : ℕ} {d : ℕ → ℝ} : ∏ t ∈ Finset.Iic k, d t = 0 := by sorry`,
);
check('prod Iic uses t \\le k', /\\prod\\limits_\{t \\le k\}/.test(prodIic), prodIic);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
