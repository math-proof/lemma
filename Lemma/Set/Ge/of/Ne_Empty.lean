import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {A : Finset ℤ}
-- given
  (h : A ≠ ∅) :
-- imply
  A.card ≥ 1 := by
-- proof
  exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)


-- created on 2020-07-12
