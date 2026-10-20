import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Statistics.GlivenkoCantelli
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Filter Function
open scoped Topology
open MathlibExt.Probability.Statistics.GlivenkoCantelliWanted


/--
[glivenko_cantelli](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Statistics/GlivenkoCantelli.lean)
-/
@[path]
private lemma glivenko_cantelli_eq
  [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}
-- given
  (hMeas : ∀ n, Measurable (X n))
  (hIndep : iIndepFun X P)
  (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P) :
-- imply
  ∀ᵐ ω ∂P, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
    |((empiricalCount X n ω x : ℝ) / ((n + 1 : ℕ) : ℝ) - (P (X 0 ⁻¹' Set.Iic x)).toReal)| <
    ε := by
-- proof
  apply MathlibExt.Probability.Statistics.GlivenkoCantelliWanted.glivenko_cantelli X hMeas hIndep hIdent


-- created on 2026-10-20
