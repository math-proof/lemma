import sympy.Basic


@[main]
private lemma main
-- given
  (A B : Set α) :
-- imply
  A \ B ⊆ A :=
-- proof
  Set.diff_subset


@[main]
private lemma fin
  [DecidableEq α]
-- given
  (A B : Finset α) :
-- imply
  A \ B ⊆ A :=
-- proof
  Finset.sdiff_subset


-- created on 2025-04-08
-- updated on 2025-07-20
