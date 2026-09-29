import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {M a b : ℝ}
-- given
  (h : |a - b| < M) :
-- imply
  |a| < max |M + b| |M - b| := by
-- proof
  obtain ⟨h₀, h₁⟩ := abs_lt.mp h
  rcases le_or_gt 0 a with ha | ha
  · rw [abs_of_nonneg ha]
    exact lt_of_lt_of_le (by linarith) ((le_abs_self (M + b)).trans (le_max_left _ _))
  · rw [abs_of_neg ha]
    exact lt_of_lt_of_le (by linarith) ((le_abs_self (M - b)).trans (le_max_right _ _))


-- created on 2026-09-27
