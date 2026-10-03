import Lemma.Set.InAdd.of.In_Icc
open Set


@[main]
private lemma main
  [Preorder α]
  [Add α]
  [AddLeftMono α]
  [AddRightMono α]
  {x a b c : α}
-- given
  (h : x ∈ Icc a b)
  (c : α) :
-- imply
  x + c ∈ Icc (a + c) (b + c) := by
-- proof
  exact InAdd.of.In_Icc h c


-- created on 2026-10-03
