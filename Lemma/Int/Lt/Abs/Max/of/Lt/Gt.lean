import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x < a)
  (h₁ : x > b) :
-- imply
  |x| < max |a| |b| := by
-- proof
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact lt_of_lt_of_le h₀ ((le_abs_self a).trans (le_max_left _ _))
  · rw [abs_of_neg hx]
    exact lt_of_lt_of_le (by linarith) ((neg_le_abs b).trans (le_max_right _ _))


-- created on 2019-12-19
