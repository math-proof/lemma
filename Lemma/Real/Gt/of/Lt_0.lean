import Mathlib.Analysis.Calculus.Deriv.MeanValue
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma monotony
  {a b : ℝ}
  {f : ℝ → ℝ}
-- given
  (h : ∀ x ∈ Set.Ico a b, deriv f x < 0)
  (h_cont : ContinuousWithinAt f (Set.Icc a b) b) :
-- imply
  ∀ x ∈ Set.Ico a b, f x > f b := by
-- proof
  have hd : ∀ x ∈ Set.Ico a b, DifferentiableAt ℝ f x := fun x hx => by
    by_contra hnd
    have := h x hx
    rw [deriv_zero_of_not_differentiableAt hnd] at this
    exact lt_irrefl _ this
  have hc : ContinuousOn f (Set.Icc a b) := by
    intro y hy
    rcases eq_or_lt_of_le hy.2 with e | hlt
    · rw [e]
      exact h_cont
    · exact (hd y ⟨hy.1, hlt⟩).continuousAt.continuousWithinAt
  have hanti : StrictAntiOn f (Set.Icc a b) := strictAntiOn_of_deriv_neg (convex_Icc a b) hc (fun x hx => by
    rw [interior_Icc] at hx
    exact h x ⟨hx.1.le, hx.2⟩)
  intro x hx
  exact hanti ⟨hx.1, hx.2.le⟩ ⟨hx.1.trans hx.2.le, le_refl b⟩ hx.2


-- created on 2020-10-16
