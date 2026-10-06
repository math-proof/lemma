import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y a b t : ℝ}
-- given
  (h : x < y)
  (_ : t ∈ Set.Ioo a b) :
-- imply
  x + t < y + t := by
-- proof
  apply add_lt_add_left h t


-- created on 2021-05-26
