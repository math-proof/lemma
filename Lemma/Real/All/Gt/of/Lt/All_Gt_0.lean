import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma monotony.right_close
  {f : ℝ → ℝ}
  {a b : ℝ}
-- given
  (_hab : a < b)
  (hc : ContinuousOn f (Set.Icc a b))
  (h : ∀ x ∈ Set.Icc a b, deriv f x > 0) :
-- imply
  ∀ x ∈ Set.Ioc a b, f x > f a := by
-- proof
  intro x hx
  have hm : StrictMonoOn f (Set.Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    (fun y hy => by rw [interior_Icc] at hy; exact h y (Set.Ioo_subset_Icc_self hy))
  exact hm ⟨le_refl a, le_trans hx.1.le hx.2⟩ (Set.Ioc_subset_Icc_self hx) hx.1


-- created on 2026-09-27
