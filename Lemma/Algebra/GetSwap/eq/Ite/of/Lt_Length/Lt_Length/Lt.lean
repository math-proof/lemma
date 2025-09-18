import Lemma.Algebra.GetSwap.eq.Get.of.Lt_LengthSwap.Lt_Length
import Lemma.Algebra.GetAppend.eq.Get.of.Lt_Length
import Lemma.Algebra.LengthAppend.eq.AddLengthS
import Lemma.Algebra.LengthTake.eq.Min_Length
import Lemma.Algebra.Le.of.Lt
import Lemma.Algebra.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.Algebra.LengthSlice.eq.SubMin
import Lemma.Algebra.LengthCons.eq.Add1Length
import Lemma.Algebra.EqAdd_Sub.of.Ge
import Lemma.Algebra.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.Algebra.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.Algebra.GetSlice.eq.Get_Add.of.Lt_LengthSlice
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Algebra.Add
import Lemma.Algebra.GetDrop.eq.Get_Add.of.Add.lt.Length
import Lemma.Algebra.LengthSwap.eq.Length
open Algebra


@[main]
private lemma main
  {a : List α}
  {i j t : ℕ}
-- given
  (h₀ : i < j)
  (h₁ : j < a.length)
  (h₂ : t < a.length) :
-- imply
  have : t < (a.swap i j).length := by simp_all [LengthSwap.eq.Length]
  (a.swap i j)[t] =
    if t = i then
      a[j]
    else if t = j then
      a[i]
    else
      a[t] := by
-- proof
  intro h₃
  have h_i := h₀.trans h₁
  let h_i := Le.of.Lt h_i
  let h_j := Le.of.Lt h₁
  have h_eq_ij : i + (1 + (j - (i + 1))) = j := by
    ring_nf
    rw [EqAdd_Sub.of.Ge]
    linarith
  have h_eq_ij' : i + ((j - (i + 1)) + 1) = j := by
    rw [Add.comm (a := 1)] at h_eq_ij
    assumption
  split_ifs with h_ti h_tj
  ·
    simp [h_ti]
    simp_all [GetSwap.eq.Get.of.Lt_LengthSwap.Lt_Length]
  ·
    simp [h_tj]
    simp_all [GetSwap.eq.Get.of.Lt_LengthSwap.Lt_Length.left]
  ·
    unfold List.swap
    split_ifs with h_eq
    ·
      rfl
    ·
      by_cases h_ti : t < i
      ·
        by_cases h_tj : t < j
        ·
          repeat rw [GetAppend.eq.Get.of.Lt_Length]
          rw [GetTake.eq.Get.of.Lt_LengthTake]
          simp_all [LengthTake.eq.Min_Length]
        ·
          linarith
      ·
        simp at h_ti
        have h_eq_ti : i + 1 + (t - i - 1) = t := by
          simp [SubSub.eq.Sub_Add.nat]
          have := Gt.of.Ge.Ne h_ti (by assumption)
          apply EqAdd_Sub.of.Ge
          linarith
        have h_lt := Gt.of.Ge.Ne h_ti (by assumption)
        by_cases h_tj : t < j
        ·
          rw [GetAppend.eq.Get.of.Lt_Length]
          rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
          rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
          rw [GetSlice.eq.Get_Add.of.Lt_LengthSlice]
          ·
            simp [h_i]
            simp [h_eq_ti]
          ·
            simp_all [LengthTake.eq.Min_Length]
          ·
            simp_all [LengthTake.eq.Min_Length]
          ·
            rw [LengthAppend.eq.AddLengthS]
            rw [LengthTake.eq.Min_Length]
            rw [LengthCons.eq.Add1Length]
            rw [LengthSlice.eq.SubMin]
            simp [h_i, h_j]
            rw [h_eq_ij]
            assumption
        ·
          simp at h_tj
          have h_gt : t > j := Gt.of.Ge.Ne h_tj (by assumption)
          have h_eq_tj : j + 1 + (t - j - 1) = t := by
            simp [SubSub.eq.Sub_Add.nat]
            have := Gt.of.Ge.Ne h_tj (by assumption)
            apply EqAdd_Sub.of.Ge
            linarith
          rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
          simp [LengthAppend.eq.AddLengthS]
          simp [LengthSlice.eq.SubMin]
          simp [h_i, h_j]
          simp [h_eq_ij']
          rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
          rw [GetDrop.eq.Get_Add.of.Add.lt.Length]
          ·
            simp [h_eq_tj]
          ·
            simp [h_eq_tj]
            assumption
          ·
            simp
            apply Gt.of.Ge.Ne h_tj (by assumption)
          ·
            rw [LengthAppend.eq.AddLengthS]
            rw [LengthTake.eq.Min_Length]
            simp [LengthSlice.eq.SubMin]
            simp [h_i, h_j]
            rw [Add.comm (b := 1)]
            rw [h_eq_ij]
            linarith


-- created on 2025-06-07
-- updated on 2025-06-28
