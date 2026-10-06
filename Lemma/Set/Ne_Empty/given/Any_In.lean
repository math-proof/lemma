import sympy.Basic


@[main]
private lemma main
  {A : Set α}
-- given
  (h : A ≠ ∅) :
-- imply
  ∃ x, x ∈ A :=
-- proof
  Set.nonempty_iff_ne_empty.mpr h


-- created on 2021-06-05
