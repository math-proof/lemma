import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : y > 0)
  (h : x ≥ y) :
-- imply
  x > 0 := by
-- proof
  exact lt_of_lt_of_le h₀ h


-- created on 2019-06-02
