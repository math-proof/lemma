import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x y : ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : y < 0) :
-- imply
  x * y > 0 := by
-- proof
  exact mul_pos_of_neg_of_neg h₀ h₁


-- created on 2020-02-03
