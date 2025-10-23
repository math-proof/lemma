import Lemma.Nat.LeAddS.is.Le
import Lemma.Nat.GtAddS.is.Gt
import Lemma.Nat.EqMax.of.Le
import Lemma.Nat.EqMax.of.Gt
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
  (a b c : α) :
-- imply
  (c + a) ⊔ (c + b) = c + a ⊔ b := by
-- proof
  by_cases h : a ≤ b
  ·
    rw [EqMax.of.Le h]
    have h' := LeAddS.of.Le.left c h
    rw [EqMax.of.Le h']
  ·
    simp at h
    rw [EqMax.of.Gt h]
    have h' := GtAddS.of.Gt.left c h
    rw [EqMax.of.Gt h']


-- created on 2025-06-18
