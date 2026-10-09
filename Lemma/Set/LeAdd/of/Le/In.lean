import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y a b t : ℝ}
-- given
  (h : x ≤ y)
  (_ : t ∈ Set.Ioo a b) :
-- imply
  x + t ≤ y + t :=
-- proof
  add_le_add_left h t


-- created on 2020-05-19
