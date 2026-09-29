import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Finset ℤ}
-- given
  (h : S.card = 1) :
-- imply
  ∃ x, S = {x} := by
-- proof
  exact Finset.card_eq_one.mp h


-- created on 2026-09-27
