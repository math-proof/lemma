import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A ∩ B = A) :
-- imply
  A ⊆ B := by
-- proof
  exact Set.inter_eq_left.mp h


-- created on 2020-11-21
