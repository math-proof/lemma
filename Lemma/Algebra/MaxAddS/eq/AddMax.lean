import Lemma.Algebra.LeAddS.is.Le
import Lemma.Algebra.GtAddS.is.Gt
import Lemma.Nat.EqMax.of.Le
import Lemma.Nat.EqMax.of.Gt
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
  (a + c) ⊔ (b + c) = a ⊔ b + c := by
-- proof
  by_cases h : a ≤ b
  ·
    rw [EqMax.of.Le h]
    have h' := LeAddS.of.Le c h
    rw [EqMax.of.Le h']
  ·
    simp at h
    rw [EqMax.of.Gt h]
    have h' := GtAddS.of.Gt c h
    rw [EqMax.of.Gt h']


-- created on 2025-06-18
