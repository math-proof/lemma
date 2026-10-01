import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x ≠ 0)
  (h₁ : a ≠ b) :
-- imply
  a * x ≠ b * x := by
-- proof
  exact fun e => h₁ (mul_right_cancel₀ h₀ e)


-- created on 2019-04-15
