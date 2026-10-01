import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a x b y : ℝ}
-- given
  (h₀ : a ≤ b)
  (h₁ : x ≤ y) :
-- imply
  a + x ≤ b + y := by
-- proof
  exact add_le_add h₀ h₁


-- created on 2019-09-27
