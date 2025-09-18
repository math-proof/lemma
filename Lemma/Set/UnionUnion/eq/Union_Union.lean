import Lemma.Basic


@[main, comm]
private lemma main
-- given
  (A B C : Set α) :
-- imply
  A ∪ B ∪ C = A ∪ (B ∪ C) :=
-- proof
  Set.union_assoc A B C


-- created on 2024-12-21
-- updated on 2025-07-20
