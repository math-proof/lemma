import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ} :
-- imply
  x < -a ∨ x > a ↔ |x| > a := by
-- proof
  constructor
  · intro h
    rcases h with h | h
    · have := neg_abs_le x
      linarith
    · have := le_abs_self x
      linarith
  · intro h
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h
      exact Or.inr h
    · rw [abs_of_neg hx] at h
      left
      linarith


-- created on 2026-09-27
