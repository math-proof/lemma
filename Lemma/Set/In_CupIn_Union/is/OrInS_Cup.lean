import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Set α)
  (f : α → Set β)
  (y : β) :
-- imply
  y ∈ ⋃ x ∈ A ∪ B, f x ↔ y ∈ ⋃ x ∈ A, f x ∨ y ∈ ⋃ x ∈ B, f x := by
-- proof
  aesop


@[main, comm, mp, mpr]
private lemma fin.fn
  [DecidableEq α]
-- given
  (A B : Finset α)
  (f : α → Finset β)
  (y : β) :
-- imply
  y ∈ ⋃ x ∈ A ∪ B, f x ↔ y ∈ ⋃ x ∈ A, f x ∨ y ∈ ⋃ x ∈ B, f x := by
-- proof
  aesop


@[main, comm, mp, mpr]
private lemma fin
  [DecidableEq α]
-- given
  (A B : Finset α)
  (f : α → Set β)
  (y : β) :
-- imply
  y ∈ ⋃ x ∈ A ∪ B, f x ↔ y ∈ ⋃ x ∈ A, f x ∨ y ∈ ⋃ x ∈ B, f x := by
-- proof
  aesop


-- created on 2025-07-20
-- updated on 2025-07-29
