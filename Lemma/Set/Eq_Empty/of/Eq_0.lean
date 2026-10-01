import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A : Finset ℤ}
-- given
  (h : A.card = 0) :
-- imply
  A = ∅ := by
-- proof
  exact Finset.card_eq_zero.mp h


-- created on 2020-07-20
