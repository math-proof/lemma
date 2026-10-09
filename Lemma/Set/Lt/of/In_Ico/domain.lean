import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h : x ∈ Set.Ico a b) :
-- imply
  a < b := by
-- proof
  exact h.1.trans_lt h.2


-- created on 2023-11-12
