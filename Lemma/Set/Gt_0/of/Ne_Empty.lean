import sympy.Basic


@[path]
private lemma main
  {A : Finset α}
-- given
  (h : A ≠ ∅) :
-- imply
  A.card > 0 :=
-- proof
  Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h)


-- created on 2020-07-12
