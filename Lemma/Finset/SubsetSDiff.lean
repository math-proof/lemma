import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
-- given
  (A B : Finset α) :
-- imply
  A \ B ⊆ A :=
-- proof
  Finset.sdiff_subset


-- created on 2025-12-30
