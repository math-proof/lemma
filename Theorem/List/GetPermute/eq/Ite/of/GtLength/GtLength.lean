module

public import Theorem.Data.List.List.Part2
public import Theorem.List.Permute.eq.Ite
public import Theorem.List.GetAppend.eq.Get.of.GtLength
public import Theorem.List.GetTake.eq.Get.of.GtLengthTake
public import Theorem.List.LengthTake.eq.Min_Length
public import Theorem.Nat.EqMin.of.Lt
public import Theorem.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
public import Theorem.List.GetSlice.eq.Get_Add.of.GtLengthSlice
public import Theorem.Nat.SubAdd.eq.Add_Sub.of.Ge
public import Theorem.Nat.AddAdd.eq.Add_Add
public import Theorem.Nat.EqSubAdd
public import Theorem.Nat.LtSub.is.Lt_Add.of.Ge
public import Theorem.List.LengthAppend.eq.AddLengthS
public import Theorem.List.LengthCons.eq.Add1Length
public import Theorem.List.LengthDrop.eq.SubLength
public import Theorem.Nat.EqAdd_Sub.of.Ge
public import Theorem.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
public import Theorem.List.GetDrop.eq.Get_Add.of.GtLength_Add
public import Theorem.Nat.Sub_Add.eq.SubSub
public import Theorem.Nat.Sub.gt.Zero.is.Gt
public import Theorem.Nat.Gt.is.Ge.Ne
public import Theorem.Nat.LeAdd_1.of.Lt
public import Theorem.Nat.Le_Sub.of.LeAdd

public section

open List Nat


public theorem List.GetPermute.eq.Ite.of.GtLength.GtLength
  {s : List α}
  {i : Fin s.length}
  {d t : ℕ}
-- given
  (h₀ : i + d < s.length)
  (h₁ : s.length > t) :
-- imply
  have : t < (s.permute i d).length := by
    rw [List.length_permute]
    omega
  (s.permute i d)[t] =
    if t < i then
      s[t]
    else if h : t < i + d then
      s[t + 1]
    else if t = i + d then
      s[i]
    else
      s[t] := by
-- proof
  intro h₁
  simp [Permute.eq.Ite]
  split_ifs with h_d
  ·
    linarith
  ·
    have h_eq_i : (i + (d + 1)) ⊓ s.length - (i + 1) = d := by
      rw [EqMin.of.Le (by linarith)]
      rw [Add.comm]
      rw [AddAdd.eq.Add_Add]
      rw [Add.comm (a := 1)]
      rw [EqSubAdd]
    apply Eq.symm
    split_ifs with h_i h_1 h_eq
    ·
      rw [GetAppend.eq.Get.of.GtLength]
      rw [GetTake.eq.Get.of.GtLengthTake]
      rw [LengthTake.eq.Min_Length]
      simp_all
    ·
      simp at h_i
      rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength]
      rw [GetAppend.eq.Get.of.GtLength]
      rw [GetSlice.eq.Get_Add.of.GtLengthSlice]
      ·
        simp [Add_Sub.eq.SubAdd.of.Ge h_i]
        simp [Add.comm]
        simp [SubAdd.eq.Add_Sub.of.Ge]
      ·
        rw [LengthSlice.eq.SubMin_Length]
        rw [h_eq_i]
        simp [LtSub.of.Lt_Add.Ge h_i h_1]
      ·
        simp_all
    ·
      repeat rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength]
      ·
        simp [LengthSlice.eq.SubMin_Length]
        simp [h_eq_i]
        simp [h_eq]
      ·
        rw [LengthSlice.eq.SubMin_Length]
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
      repeat rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength]
      simp [LengthSlice.eq.SubMin_Length]
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
        rw [LengthSlice.eq.SubMin_Length]
        rw [h_eq_i]
        simp [GeSub.of.Ge_Add.left h_1]
      ·
        simp_all


-- created on 2025-06-08
-- updated on 2026-11-07
