import sympy.Basic


@[main]
private lemma main
  [DecidableEq ι]
-- given
  (A B : Finset ι)
  (x : ι) :
-- imply
  x ∈ A ∩ B ∧ x ∈ A \ B ↔ False := by
-- proof
  aesop


-- created on 2025-12-30
