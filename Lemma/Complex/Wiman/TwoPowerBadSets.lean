import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Complex.Wiman.TwoPowerBadSets
open Filter MeasureTheory Set
open scoped ENNReal
open Complex


/--
[exists_finite_wimanExceptionalSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/TwoPowerBadSets.lean)
-/
@[path]
private lemma exists_finite_wimanExceptionalSet_eq
  {f : ℂ → ℂ}
-- given
  (hf : Differentiable ℂ f)
  (htrans : IsTranscendental f) :
-- imply
  ∃ x₀ : ℝ,
    volume (wimanExceptionalSet f x₀) < ∞ ∧
    ∀ x, x₀ ≤ x → x ∉ wimanExceptionalSet f x₀ →
    iteratedDeriv 2 (wimanGrowth f) x ≤
    wimanGrowth f x ^ (81 / 64 : ℝ) := by
-- proof
  apply Complex.exists_finite_wimanExceptionalSet f hf htrans


-- created on 2026-10-20
