import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
  -- given
  (h1 : x ≤ a)
  (h2 : b ≤ y)
  -- imply
  : x + b ≤ a + y := by
  -- proof
  exact add_le_add h1 h2

-- created on 2018-09-01
