import Lemma.Basic


@[main]
private lemma main
-- given
  (f : α → Set β):
-- imply
  ⋃ x ∈ ({a} : Set α), f x = f a := by
-- proof
  simp


@[main]
private lemma fin.fn
  [DecidableEq α]
-- given
  (f : α → Finset β)
  (a : α) :
-- imply
  ⋃ k ∈ ({a} : Finset α), f k = (f a : Set β) := by
-- proof
  simp


@[main]
private lemma fin
  [DecidableEq α]
-- given
  (f : α → Set β)
  (a : α) :
-- imply
  ⋃ k ∈ ({a} : Finset α), f k = f a := by
-- proof
  simp


-- created on 2025-08-14
