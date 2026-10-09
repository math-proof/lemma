import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
-- given
  (hx : x ≥ 0)
  (h : x ≤ a)
  (n : ℕ) :
-- imply
  x ^ n ≤ a ^ n := by
-- proof
  exact pow_le_pow_left₀ hx h n


-- created on 2023-04-15
