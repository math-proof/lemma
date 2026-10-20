import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.LogMajorantRegularity
open Filter MeasureTheory Set
open Complex


/--
[eventually_wimanGrowth_regular](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/LogMajorantRegularity.lean)
-/
@[path]
private lemma eventually_wimanGrowth_regular_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∃ x₀ : ℝ,
    (∀ x, x₀ ≤ x → 0 < wimanGrowth f x) ∧
    MonotoneOn (wimanGrowth f) (Set.Ici x₀) ∧
    MonotoneOn (deriv (wimanGrowth f)) (Set.Ici x₀) ∧
    ContDiff ℝ 2 (wimanGrowth f) ∧
    Tendsto (deriv (wimanGrowth f)) atTop atTop := by
-- proof
  apply Complex.eventually_wimanGrowth_regular f hf htrans


-- created on 2026-10-20
