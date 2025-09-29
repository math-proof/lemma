import sympy.Basic


@[main]
private lemma main
-- given
  (S : Set α) :
-- imply
  S = ∅ ∨ ∃ x, x ∈ S :=
-- proof
  Set.eq_empty_or_nonempty S


-- created on 2025-09-29
