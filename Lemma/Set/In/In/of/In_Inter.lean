import sympy.Basic


@[main]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A ∧ x ∈ B := by
-- proof
  simp_all


@[main]
private lemma fin
  [DecidableEq α]
  {x : α}
  {A B : Finset α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A ∧ x ∈ B := by
-- proof
  simp_all


-- created on 2025-07-19
