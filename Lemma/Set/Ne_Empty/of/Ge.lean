import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {S : Finset ℤ}
-- given
  (h : S.card ≥ 1) :
-- imply
  S ≠ ∅ := by
-- proof
  exact Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp h)


-- created on 2020-07-15
