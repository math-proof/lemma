import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≥ 0)
  (h₁ : x < y) :
-- imply
  min (y ^ 2) (x ^ 2) = x ^ 2 := by
-- proof
  exact min_eq_right (by nlinarith)


-- created on 2019-07-02
