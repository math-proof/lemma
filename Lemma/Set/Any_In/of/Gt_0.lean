import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A : Finset ℤ}
-- given
  (h : A.card > 0) :
-- imply
  ∃ x, x ∈ A := by
-- proof
  exact Finset.card_pos.mp h


-- created on 2020-07-13
