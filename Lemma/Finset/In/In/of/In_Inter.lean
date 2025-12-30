import sympy.Basic


@[main]
private lemma main
  [DecidableEq α]
  {x : α}
  {A B : Finset α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A ∧ x ∈ B := by
-- proof
  simp_all


-- created on 2025-12-30
