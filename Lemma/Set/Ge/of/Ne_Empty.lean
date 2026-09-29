import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A : Finset ℤ}
-- given
  (h : A ≠ ∅) :
-- imply
  A.card ≥ 1 := by
-- proof
  exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)


-- created on 2026-09-27
