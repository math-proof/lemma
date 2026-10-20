import Mathlib
import sympy.Basic
import sympy.atlas.Probability.LawIteratedLogarithm
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal
open MathlibExt.Probability.LawIteratedLogarithmWanted


/--
[law_of_the_iterated_logarithm_of_memLp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LawIteratedLogarithm.lean)
-/
@[path]
private lemma law_of_the_iterated_logarithm_of_memLp_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
-- given
  (hMeas : ∀ n, Measurable (X n))
  (hIndep : iIndepFun X μ)
  (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
  (hMemLp : MemLp (X 0) 2 μ)
  (hMean : μ[X 0] = 0)
  (hVar : Var[X 0; μ] = 1) :
-- imply
  ∀ᵐ ω ∂μ,
    Filter.limsup (fun n : ℕ =>
    (∑ i ∈ Finset.range n, X i ω) /
    Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (1 : ℝ)
    ∧ Filter.liminf (fun n : ℕ =>
    (∑ i ∈ Finset.range n, X i ω) /
    Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (-1 : ℝ) := by
-- proof
  apply MathlibExt.Probability.LawIteratedLogarithmWanted.law_of_the_iterated_logarithm_of_memLp X hMeas hIndep hIdent hMemLp hMean hVar

/--
[law_of_the_iterated_logarithm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/LawIteratedLogarithm.lean)
-/
@[path]
private lemma law_of_the_iterated_logarithm_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : ℕ → Ω → ℝ}
-- given
  (hMeas : ∀ n, Measurable (X n))
  (hIndep : iIndepFun X μ)
  (hIdent : ∀ i, IdentDistrib (X i) (X 0) μ μ)
  (hInt : Integrable (X 0) μ)
  (hMemLp : MemLp (X 0) 2 μ)
  (hMean : μ[X 0] = 0)
  (hVar : Var[X 0; μ] = 1) :
-- imply
  ∀ᵐ ω ∂μ,
    Filter.limsup (fun n : ℕ =>
    (∑ i ∈ Finset.range n, X i ω) /
    Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (1 : ℝ)
    ∧ Filter.liminf (fun n : ℕ =>
    (∑ i ∈ Finset.range n, X i ω) /
    Real.sqrt (2 * (n : ℝ) * Real.log (Real.log (n : ℝ)))) Filter.atTop = (-1 : ℝ) := by
-- proof
  apply MathlibExt.Probability.LawIteratedLogarithmWanted.law_of_the_iterated_logarithm X hMeas hIndep hIdent hInt hMemLp hMean hVar


-- created on 2026-10-20
