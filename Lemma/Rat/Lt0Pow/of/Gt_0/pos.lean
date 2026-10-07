import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
  {n : ℕ}
  -- given
  (hx : 0 < x)
  (_hn : 0 < n)
  -- imply
  : 0 < x ^ n := by
  -- proof
  exact pow_pos hx n

-- created on 2023-04-15
