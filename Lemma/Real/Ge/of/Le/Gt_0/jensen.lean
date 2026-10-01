import Mathlib.Analysis.Convex.Deriv
import sympy.Basic


/--
Jensen's inequality (two-point form): if `f'' > 0` on `(a, b)`, `x₀ ≤ x₁` are in `(a, b)`
and `w ∈ [0, 1]`, then `w * f x₀ + (1 - w) * f x₁ ≥ f (w * x₀ + (1 - w) * x₁)`.
-/
@[main]
private lemma main
  {a b : ℝ}
  {f : ℝ → ℝ}
  {x₀ x₁ : ℝ}
  {w : ℝ}
-- given
  (h₁ : ContinuousOn f (Set.Ioo a b))
  (h₂ : ∀ x ∈ Set.Ioo a b, 0 < deriv^[2] f x)
  (h₃ : w ∈ Set.Icc (0 : ℝ) 1)
  (h₄ : x₀ ∈ Set.Ioo a b)
  (h₅ : x₁ ∈ Set.Ioo a b) :
-- imply
  w * f x₀ + (1 - w) * f x₁ ≥ f (w * x₀ + (1 - w) * x₁) := by
-- proof
  have h := (strictConvexOn_of_deriv2_pos' (convex_Ioo a b) h₁ h₂).convexOn.2 h₄ h₅ h₃.1 (sub_nonneg.mpr h₃.2) (by ring)
  simpa [smul_eq_mul] using h


-- created on 2020-05-11
