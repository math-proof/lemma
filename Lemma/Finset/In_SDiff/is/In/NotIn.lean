import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [DecidableEq α]
-- given
  (x : α)
  (A B : Finset α) :
-- imply
  x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by
-- proof
  simp_all


-- created on 2025-12-30
