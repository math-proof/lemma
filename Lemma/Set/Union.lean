import Lemma.Basic


@[main]
private lemma comm.finset
  [DecidableEq ι]
  {a b : Finset ι} :
-- imply
  a ∪ b = b ∪ a := by
-- proof
  rw [Finset.union_comm]


@[main]
private lemma Comm
  {a b : Set α} :
-- imply
  a ∪ b = b ∪ a := by
-- proof
  rw [Set.union_comm]


-- created on 2025-06-06
