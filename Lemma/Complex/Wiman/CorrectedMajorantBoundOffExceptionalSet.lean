import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.CorrectedMajorantBoundOffExceptionalSet
open Filter MeasureTheory Set
open scoped ENNReal
open Complex


/--
[wimanMajorant_bound_off_exceptionalSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/CorrectedMajorantBoundOffExceptionalSet.lean)
-/
@[path]
private lemma wimanMajorant_bound_off_exceptionalSet_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∃ C x₀ : ℝ, 0 < C ∧
    volume (wimanExceptionalSet f x₀) < ∞ ∧
    ∀ x, x₀ ≤ x → x ∉ wimanExceptionalSet f x₀ →
    wimanMajorant f (Real.exp x) ≤
    C * wimanMaximumTerm f (Real.exp x) *
    (1 + wimanGrowth f x ^ (81 / 128 : ℝ)) := by
-- proof
  apply Complex.wimanMajorant_bound_off_exceptionalSet f hf htrans


-- created on 2026-10-20
