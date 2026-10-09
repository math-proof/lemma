import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (h : |x| > a) :
-- imply
  x < -a ∨ x > a := by
-- proof
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx] at h
    exact Or.inr h
  · rw [abs_of_neg hx] at h
    left
    linarith


-- created on 2018-07-31
