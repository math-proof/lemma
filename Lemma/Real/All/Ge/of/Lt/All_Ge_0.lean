import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma monotony.right_close
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (_hab : a < b)
  (hc : ContinuousOn f (Set.Icc a b))
  (hd : DifferentiableOn ℝ f (Set.Ioo a b))
  (h : ∀ x ∈ Set.Icc a b, deriv f x ≥ 0) :
-- imply
  ∀ x ∈ Set.Icc a b, f x ≥ f a := by
-- proof
  intro x hx
  have hm : MonotoneOn f (Set.Icc a b) := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc (by rwa [interior_Icc])
    (fun y hy => by rw [interior_Icc] at hy; exact h y (Set.Ioo_subset_Icc_self hy))
  exact hm ⟨le_refl a, le_trans hx.1 hx.2⟩ hx hx.1


-- created on 2026-09-27
