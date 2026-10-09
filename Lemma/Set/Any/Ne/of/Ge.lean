import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Finset ℤ}
-- given
  (h : S.card ≥ 2) :
-- imply
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
-- proof
  exact Finset.one_lt_card.mp (by omega)


-- created on 2020-07-15
