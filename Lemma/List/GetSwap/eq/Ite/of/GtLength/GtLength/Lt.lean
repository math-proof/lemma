import Lemma.List.GetSwap.eq.Get.of.Lt_LengthSwap.GtLength
import Lemma.List.GetAppend.eq.Get.of.GtLength
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.Nat.Le.of.Lt
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.List.GetSlice.eq.Get_Add.of.Lt_LengthSlice
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.List.GetDrop.eq.Get_Add.of.GtLength_Add
import Lemma.List.LengthSwap.eq.Length
open List Nat


@[main]
private lemma main
  {a : List α}
  {i j t : ℕ}
-- given
  (h₀ : i < j)
  (h₁ : a.length > j)
  (h₂ : a.length > t) :
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
    grind
  have h_eq_ij' : i + ((j - (i + 1)) + 1) = j := by
    grind
  split_ifs with h_ti h_tj
  ·
    simp_all [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength]
  ·
    simp_all [GetSwap.eq.Get.of.Lt_LengthSwap.GtLength.left]
  ·
    unfold List.swap
    split_ifs with h_eq
    ·
      rfl
    ·
      if h_ti : t < i then
        grind
      else
        simp at h_ti
        have h_eq_ti : i + 1 + (t - i - 1) = t := by
          grind
        have h_lt := Gt.of.Ge.Ne h_ti (by assumption)
        if h_tj : t < j then
          rw [GetAppend.eq.Get.of.GtLength]
          rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
          rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
          rw [GetSlice.eq.Get_Add.of.Lt_LengthSlice]
          repeat grind
          rw [LengthAppend.eq.AddLengthS]
          rw [LengthCons.eq.Add1Length]
          rw [LengthSlice.eq.SubMin]
          grind
        else
          simp at h_tj
          have h_gt : t > j := Gt.of.Ge.Ne h_tj (by assumption)
          have h_eq_tj : j + 1 + (t - j - 1) = t := by
            grind
          rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
          simp [LengthSlice.eq.SubMin]
          simp [h_i, h_j]
          simp [h_eq_ij']
          rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
          rw [GetDrop.eq.Get_Add.of.GtLength_Add] <;>
            simp [h_eq_tj]
          ·
            assumption
          ·
            grind
          ·
            simp [LengthSlice.eq.SubMin]
            grind


-- created on 2025-06-07
-- updated on 2025-10-25
