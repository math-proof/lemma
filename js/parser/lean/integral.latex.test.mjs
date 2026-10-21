/**
 * Integral binder/measure latex: subscript binder; no trailing dω when ∂μ present.
 * Run: `node js/parser/lean/integral.latex.test.mjs`
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

function intLatex(src) {
  const root = compile(src);
  const walk = (n, out = []) => {
    if (!n || typeof n !== 'object') return out;
    if (n.constructor?.name === 'Lean_int') out.push(n);
    for (const c of [n.bound, n.scope, n.lhs, n.rhs, n.arg, ...(Array.isArray(n.args) ? n.args : [])].filter(Boolean))
      walk(c, out);
    return out;
  };
  const ints = walk(root);
  return ints[0]?.toLatex() ?? '';
}

const binderPartial = implyLatex(
  `lemma t1 (μ : Measure Ω) (f : Ω → ℝ) : ∫ ω, f ω ∂μ = 0 := by sorry`,
);
check('binder+∂μ uses int subscript', binderPartial.includes('\\int_{ω}'));
check('binder+∂μ uses blue partial', /\\color\{blue\}\\partial/.test(binderPartial));
check('binder+∂μ has no mathrm d', !/mathrm\{d\}/.test(binderPartial));

const binderOnly = implyLatex(
  `lemma t2 (f : Ω → ℝ) : ∫ ω, f ω = 0 := by sorry`,
);
check('binder only uses int subscript', binderOnly.includes('\\int_{ω}'));
check('binder only has no mathrm d', !/mathrm\{d\}/.test(binderOnly));

const domain = implyLatex(
  `lemma t3 (f : ℝ → ℝ) : ∫ x in (0)..1, f x = 0 := by sorry`,
);
check('domain upto keeps limits', domain.includes('\\int\\limits_'));
check('domain upto keeps mathrm d', /mathrm\{d\}/.test(domain));

const nested = intLatex(`
lemma t4 {M : Measure Ω} {γ : ℝ} {n : ℕ} {Q : ℕ → Ω → ℝ} {s : ℕ → Ω → ℕ} {θ : ℕ} :
  ∫ ω, ∑ t ∈ Finset.range n, (γ ^ t * Q t ω) • ∇[θ] (Real.log (s t ω)) ∂(M θ) = 0 := by sorry
`);
check('nested ∑•∇ ∂μ: subscript binder', nested.includes('\\int_{ω}'));
check('nested ∑•∇ ∂μ: blue partial only', /\\color\{blue\}\\partial/.test(nested));
check('nested ∑•∇ ∂μ: no mathrm d', !/mathrm\{d\}/.test(nested));
check(
  'nested ∑•∇ ∂μ: no stray body partial',
  (nested.match(/\\partial/g) || []).length === 1,
  nested.slice(-120),
);

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
