import Lemma.Basic


@[main]
private lemma fin
  {A B : Finset ι}
-- given
  (h : A = B)
  (x : ι):
-- imply
  x ∈ A ↔ x ∈ B := by
-- proof
  rw [h]


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A = B)
  (x : α):
-- imply
  x ∈ A ↔ x ∈ B := by
-- proof
  rw [h]


-- created on 2025-04-30
