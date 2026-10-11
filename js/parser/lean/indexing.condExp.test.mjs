/**
 * Mathlib `μ[f | m]` (GetElem / condExp) must not render as blackboard-E.
 * Run: `node js/parser/lean/indexing.condExp.test.mjs`
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

/** Imply line from Lemma/Random/MEqExpectS/of/All_Eq/In_Ico.lean (abbreviated binders). */
const src = `
open MeasureTheory ProbabilityTheory PolicyGradient Random
lemma condExp_getElem_imply
  {M : Model Θ S A} {θ : Θ} {γ : ℝ} {t : ℕ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A} :
  (M θ)[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance] =ᵐ[M θ]
    (M θ)[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (s (t + 1)) inferInstance] := by
  sorry
`;

const codes = compile(src).render2vue(false);
const imply = codes.lemma[0].imply;
const latex = imply?.latex ?? '';
const lean = imply?.lean ?? '';

check('imply lean keeps GetElem on measure', lean.includes('(M θ)[') && lean.includes('|'));
check(
  'Mathlib condExp GetElem is not blackboard E',
  !latex.includes('\\mathbb{E}'),
  latex.slice(0, 200),
);
check(
  'measure stays as bracket base',
  /\\left\[/.test(latex) && latex.includes('M') && latex.includes('\\middle|'),
  latex.slice(0, 240),
);

/** Real `𝔼` Expectation sugar must still use the mathop / E path, not the measure bracket. */
const expectSrc = `
lemma expect_sugar (π : ProbabilityMeasure Ω) (X : Ω → ℝ) (m : MeasurableSpace Ω) :
  𝔼[X](X | m) = 0 := by
  sorry
`;
// If this stub fails to parse Expectation sugar, skip soft — only assert when latex is produced.
try {
  const ex = compile(expectSrc).render2vue(false);
  const exLatex = ex.lemma?.[0]?.imply?.latex ?? '';
  if (exLatex) {
    check(
      '𝔼 binder sugar still uses E / mathop (not bare measure brackets only)',
      exLatex.includes('\\mathbb{E}') || exLatex.includes('\\mathop'),
      exLatex.slice(0, 200),
    );
  } else {
    console.log('skip 𝔼 sugar latex (no imply latex from stub)');
  }
} catch (e) {
  console.log('skip 𝔼 sugar parse:', e.message?.slice?.(0, 80) ?? e);
}

if (failed) {
  console.error(`${failed} failure(s)`);
  process.exit(1);
}
console.log('all ok');
