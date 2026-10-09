import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b : ℝ}
-- given
  (h₀ : x > a)
  (h₁ : y > b) :
-- imply
  max x y > max a b := by
-- proof
  exact max_lt (lt_max_of_lt_left h₀) (lt_max_of_lt_right h₁)


-- created on 2019-03-09
