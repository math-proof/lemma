import sympy.Basic


@[main]
private lemma main
-- given
  (A B : Set α)
  (x : α) :
-- imply
  x ∈ A ∩ B ∧ x ∈ A \ B ↔ False := by
-- proof
  aesop


-- created on 2025-10-01
