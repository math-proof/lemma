import sympy.Basic


@[main]
private lemma main
  {A : Finset α}
-- given
  (h : A ≠ ∅) :
-- imply
  A.card ≠ 0 :=
-- proof
  Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr h)


-- created on 2026-09-27
