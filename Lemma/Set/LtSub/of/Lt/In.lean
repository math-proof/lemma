import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b t : ℝ}
-- given
  (h : x < y)
  (_ : t ∈ Set.Ioo a b) :
-- imply
  x - t < y - t := by
-- proof
  apply sub_lt_sub_right h t


-- created on 2021-05-26
