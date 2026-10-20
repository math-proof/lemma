import Mathlib
import sympy.Basic
import sympy.atlas.Probability.HoeffdingBinomialLowerTail
open scoped BigOperators
open ProbabilityTheory


/--
[hoeffding_binomial_lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/HoeffdingBinomialLowerTail.lean)
-/
@[path]
private lemma hoeffding_binomial_lower_tail_eq
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → ℝ}
  {p ε : ℝ}
-- given
  (h_indep : ProbabilityTheory.iIndepFun X μ)
  (hmeas : ∀ i, AEMeasurable (X i) μ)
  (hBernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
  (hexp : ∀ i, ∫ x, X i x ∂μ = p)
  (hε : 0 < ε) :
-- imply
  μ.real {ω | (∑ i, X i ω) ≤ (n : ℝ) * (p - ε)} ≤
    Real.exp (-2 * ε ^ 2 * (n : ℝ)) := by
-- proof
  apply ProbabilityTheory.hoeffding_binomial_lower_tail X p ε h_indep hmeas hBernoulli hexp hε


-- created on 2026-10-20
