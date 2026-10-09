import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  b > x := by
-- proof
  exact h.2


@[path]
private lemma domain
  {x a b : ℤ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  b > a := by
-- proof
  exact lt_of_le_of_lt h.1 h.2


-- created on 2023-05-03
