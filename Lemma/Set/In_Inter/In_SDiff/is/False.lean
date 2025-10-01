import sympy.Basic


@[main]
private lemma fin
  [DecidableEq ι]
-- given
  (A B : Finset ι)
  (x : ι) :
-- imply
  x ∈ A ∩ B ∧ x ∈ A \ B ↔ False := by
-- proof
  aesop


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
