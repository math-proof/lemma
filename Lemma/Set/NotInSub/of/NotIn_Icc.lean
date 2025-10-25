import Lemma.Set.InAdd.of.In_Icc
import Lemma.Int.EqAddSub
open Set Int


@[main]
private lemma main
  [Preorder α]
  [AddGroup α]
  [AddLeftMono α]
  [AddRightMono α]
  {a b x t : α}
-- given
  (h : x ∉ Icc a b) :
-- imply
  x - t ∉ Icc (a - t) (b - t) := by
-- proof
  contrapose! h
  have h := InAdd.of.In_Icc h t
  repeat rw [EqAddSub] at h
  assumption


-- created on 2025-08-02
