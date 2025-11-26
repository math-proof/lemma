import stdlib.List
import Lemma.List.Swap.eq.Ite
import Lemma.List.LengthSwap.eq.Length
import Lemma.Nat.Ge.of.NotLt
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Nat.Ge.of.Gt
import Lemma.List.GetSwap.eq.Get.of.Lt_LengthSwap.GtLength
import Lemma.List.EqAppend_ConsAppend_Cons.of.GtLength.Lt
import Lemma.List.EqSwapS
open List Nat


@[main]
private lemma main
-- given
  (a : List α)
  (i j : ℕ) :
-- imply
  (a.swap i j).swap j i = a := by
-- proof
  rw [Swap.eq.Ite]
  simp [LengthSwap.eq.Length]
  split_ifs with h_eq h_lt? h_i h_j
  ·
    rw [h_eq]
    simp [List.swap]
  ·
    rw [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength (by linarith) (by linarith)]
    rw [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength.left h_i (by linarith)]
    rw [EqSwapS]
    apply EqAppend_ConsAppend_Cons.of.GtLength.Lt h_lt? h_i
  ·
    unfold List.swap
    simp [h_i]
    have h_ge := Ge.of.Gt h_lt?
    simp [h_ge]
  ·
    have h_ge := Ge.of.NotLt h_lt?
    have h_gt := Gt.of.Ge.Ne h_ge h_eq
    rw [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength h_j (by linarith)]
    rw [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength.left (by linarith) (by linarith)]
    apply EqAppend_ConsAppend_Cons.of.GtLength.Lt h_gt h_j
  ·
    unfold List.swap
    simp [h_j]
    have h_ge := Ge.of.NotLt h_lt?
    have h_gt := Gt.of.Ge.Ne h_ge h_eq
    simp [h_gt]


@[main]
private lemma swap
-- given
  (a : List α)
  (i j : ℕ) :
-- imply
  (a.swap i j).swap i j = a := by
-- proof
  have := main a i j
  rwa [EqSwapS _ j i] at this


-- created on 2025-05-17
-- updated on 2025-05-18
