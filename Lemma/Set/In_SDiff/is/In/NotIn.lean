import Lemma.Basic


@[main, comm, mp, mpr]
private lemma fin
  [DecidableEq α]
-- given
  (x : α)
  (A B : Finset α) :
-- imply
  x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by
-- proof
  simp_all


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : α)
  (A B : Set α) :
-- imply
  x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by
-- proof
  simp_all


-- created on 2025-05-18
