import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {A : Finset ℤ}
-- given
  (h : A.card > 0) :
-- imply
  A ≠ ∅ := by
-- proof
  exact Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)


-- created on 2020-07-13
