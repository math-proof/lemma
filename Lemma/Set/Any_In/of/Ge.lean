import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {S : Finset ℤ}
-- given
  (h : S.card ≥ 1) :
-- imply
  ∃ x, x ∈ S := by
-- proof
  exact Finset.card_pos.mp h


-- created on 2026-09-27
