import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x a : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : x ≥ a) :
-- imply
  1 / x ≤ 1 / a := by
-- proof
  exact one_div_le_one_div_of_le h₀ h₁


-- created on 2019-08-09
