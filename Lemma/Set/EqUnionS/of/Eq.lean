import Lemma.Basic


@[main]
private lemma main
  {A B : Set α}
-- given
  (h : A = B) 
  (X : Set α):
-- imply
  A ∪ X = B ∪ X := by
-- proof
  rw [h]


-- created on 2025-07-20
-- updated on 2025-08-04
