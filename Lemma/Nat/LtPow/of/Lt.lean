import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a : ℝ}
  {n : ℕ}
-- given
  (hn : n > 0)
  (hx : x ≥ 0)
  (h : x < a) :
-- imply
  x ^ n < a ^ n := by
-- proof
  exact pow_lt_pow_left₀ h hx (by omega)


-- created on 2023-04-15
