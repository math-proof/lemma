import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : x ≤ a)
  (h₁ : b ≤ y) :
-- imply
  x + b ≤ a + y :=
-- proof
  add_le_add h₀ h₁


-- created on 2018-06-07
