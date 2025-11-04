import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.EqMin.of.Gt
import Lemma.Nat.GtAddS.is.Gt
open Nat


@[main]
private lemma main
  [LinearOrder α]
  [Add α]
  [AddLeftMono α]
  [AddRightMono α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
-- given
  (a b c: α) :
-- imply
  (a + c) ⊓ (b + c) = a ⊓ b + c := by
-- proof
  if h : a ≤ b then
    rw [EqMin.of.Le h]
    have h' := LeAddS.of.Le c h
    rw [EqMin.of.Le h']
  else
    simp at h
    rw [EqMin.of.Gt h]
    have h' := GtAddS.of.Gt c h
    rw [EqMin.of.Gt h']


-- created on 2025-06-18
