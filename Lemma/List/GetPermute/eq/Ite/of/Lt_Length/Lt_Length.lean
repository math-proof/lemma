import Lemma.List.Permute.eq.Ite
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Nat.EqMin.of.Lt
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.List.GetSlice.eq.Get_Add.of.Lt_LengthSlice
import Lemma.Nat.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.Add
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.EqMin.of.Le
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqSubAdd
import Lemma.Nat.LtSub.is.Lt_Add.of.Ge
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.Nat.EqAdd_Sub.of.Ge
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.List.GetDrop.eq.Get_Add.of.GtLength_Add
import Lemma.Nat.Sub_Add.eq.SubSub
import Lemma.Nat.Sub.gt.Zero.is.Gt
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Nat.LeAdd_1.of.Lt
import Lemma.Nat.GeSub.of.Ge_Add
open List Nat


@[main]
private lemma main
  {a : List α}
  {i : Fin a.length}
  {d t : ℕ}
-- given
  (h₀ : i + d < a.length)
  (h₁ : t < a.length) :
-- imply
  have : t < (a.permute i d).length := by simp_all
  (a.permute i d)[t] =
    if t < i then
      a[t]
    else if h : t < i + d then
      a[t + 1]
    else if t = i + d then
      a[i]
    else
      a[t] := by
-- proof
  intro h₁
  simp [Permute.eq.Ite]
  split_ifs with h_d
  ·
    linarith
  ·
    have h_eq_i : (i + (d + 1)) ⊓ a.length - (i + 1) = d := by
      rw [EqMin.of.Le (by linarith)]
      rw [Add.comm]
      rw [AddAdd.eq.Add_Add]
      rw [Add.comm (a := 1)]
      rw [EqSubAdd]
    apply Eq.symm
    split_ifs with h_i h_1 h_eq
    ·
      rw [GetAppend.eq.Get.of.Lt_Length]
      rw [GetTake.eq.Get.of.Lt_LengthTake]
      rw [LengthTake.eq.Min_Length]
      simp_all
    ·
      simp at h_i
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
      rw [GetAppend.eq.Get.of.Lt_Length]
      rw [GetSlice.eq.Get_Add.of.Lt_LengthSlice]
      ·
        simp [Add_Sub.eq.SubAdd.of.Ge h_i]
        simp [Add.comm]
        simp [SubAdd.eq.Add_Sub.of.Ge]
      ·
        rw [LengthSlice.eq.SubMin]
        rw [h_eq_i]
        simp [LtSub.of.Lt_Add.Ge h_i h_1]
      ·
        simp_all
    ·
      repeat rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
      ·
        simp [LengthSlice.eq.SubMin]
        simp [h_eq_i]
        simp [h_eq]
      ·
        rw [LengthSlice.eq.SubMin]
        rw [h_eq_i]
        simp [h_eq]
      ·
        simp_all
    ·
      simp at h_i h_1 h_eq
      have h_eq_t : ↑i + (d + 1) + (t - ↑i - d - 1) = t := by
        rw [Add_Add.eq.AddAdd]
        simp [SubSub.eq.Sub_Add]
        rw [EqAdd_Sub.of.Ge]
        apply Ge_Add_1.of.Gt
        apply Gt.of.Ge.Ne h_1 h_eq
      repeat rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
      simp [LengthSlice.eq.SubMin]
      simp [h_eq_i]
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
      rw [GetDrop.eq.Get_Add.of.GtLength_Add]
      ·
        simp [h_eq_t]
      ·
        simp_all
      ·
        rw [SubSub.eq.Sub_Add]
        apply Sub.gt.Zero.of.Gt
        apply Gt.of.Ge.Ne h_1 h_eq
      ·
        rw [LengthSlice.eq.SubMin]
        rw [h_eq_i]
        simp [GeSub.of.Ge_Add.left h_1]
      ·
        simp_all


-- created on 2025-06-08
-- updated on 2025-06-28
