import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma monotony
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (h : ∀ x ∈ Set.Icc a b, deriv f x > 0) :
-- imply
  ∀ x ∈ Set.Icc a b, f x ≤ f b := by
-- proof
  have hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x := fun x hx => by
    by_contra hnd
    have := h x hx
    rw [deriv_zero_of_not_differentiableAt hnd] at this
    exact lt_irrefl _ this
  have hc : ContinuousOn f (Set.Icc a b) := fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn f (Set.Icc a b) := strictMonoOn_of_deriv_pos (convex_Icc a b) hc (fun x hx => by
    rw [interior_Icc] at hx
    exact h x ⟨hx.1.le, hx.2.le⟩)
  intro x hx
  exact hmono.monotoneOn hx ⟨hx.1.trans hx.2, le_refl b⟩ hx.2


-- created on 2020-10-19
