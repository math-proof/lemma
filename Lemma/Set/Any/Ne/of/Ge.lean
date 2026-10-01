import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Finset ℤ}
-- given
  (h : S.card ≥ 2) :
-- imply
  ∃ x ∈ S, ∃ y ∈ S, x ≠ y := by
-- proof
  exact Finset.one_lt_card.mp (by omega)


-- created on 2026-09-27
