import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (ha : a ≥ 0)
  (h : x ≥ a)
  (n : ℕ) :
-- imply
  x ^ n ≥ a ^ n := by
-- proof
  exact pow_le_pow_left₀ ha h n


-- created on 2023-04-15
