import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A B : Set α}
-- given
  (h : A ⊆ B) :
-- imply
  A ∩ B = A := by
-- proof
  apply Set.inter_eq_left.mpr h


-- created on 2020-11-20
