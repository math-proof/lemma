import Lemma.Nat.EqMin.of.Le
import Lemma.Algebra.LeAddS.is.Le
import Lemma.Nat.EqMin.of.Gt
import Lemma.Algebra.GtAddS.is.Gt
open Algebra Nat


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
  (c + a) ⊓ (c + b) = c + a ⊓ b := by
-- proof
  by_cases h : a ≤ b
  ·
    rw [EqMin.of.Le h]
    have h' := LeAddS.of.Le.left c h
    rw [EqMin.of.Le h']
  ·
    simp at h
    rw [EqMin.of.Gt h]
    have h' := GtAddS.of.Gt.left c h
    rw [EqMin.of.Gt h']


-- created on 2025-06-18
