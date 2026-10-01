import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A B : Finset ℤ}
-- given
  (h : 0 = (B \ A).card) :
-- imply
  B ⊆ A := by
-- proof
  exact Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h.symm)


-- created on 2020-09-06
