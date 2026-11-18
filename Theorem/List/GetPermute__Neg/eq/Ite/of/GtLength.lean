module

public import Theorem.Data.List.List.Part2
public import Theorem.List.Permute.eq.Ite
public import Theorem.List.GetAppend.eq.Get.of.GtLength
public import Theorem.Nat.EqMin.of.Lt
public import Theorem.List.GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength
public import Theorem.List.LengthAppend.eq.AddLengthS
public import Theorem.List.LengthCons.eq.Add1Length
public import Theorem.List.Slice.eq.Nil
public import Theorem.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
public import Theorem.List.GetSlice.eq.Get_Add.of.GtLengthSlice
public import Theorem.Nat.LeSub.is.Le_Add
public import Theorem.Nat.Lt.is.Le.Ne
public import Theorem.Nat.Sub.ge.One.of.Gt
public import Theorem.Nat.LtSub

public import Theorem.List.LengthSlice.eq.SubMin_Length
public section

open List Nat Matrix


public theorem List.GetPermute__Neg.eq.Ite.of.GtLength
  {s : List α}
-- given
  (h : s.length > t)
  (i : Fin s.length)
  (d : ℕ):
-- imply
  have : t < (s.permute i (-d)).length := by
    rw [List.length_permute]
    exact h
  (s.permute i (-d))[t] =
    if t < i - d then
      s[t]
    else if t = i - d then
      s[i]
    else if t ≤ i then
      s[t - 1]
    else
      s[t] := by
-- proof
  have h_sub := LtSub i d
  simp [Permute.eq.Ite]
  split_ifs with h_d
  ·
    have h_t : t < (s.take (i - d)).length + (s[(i : ℕ)] :: (s.slice (i - d) i ++ s.drop (i + 1))).length := by
      rw [LengthCons.eq.Add1Length]
      rw [LengthAppend.eq.AddLengthS]
      rw [LengthSlice.eq.SubMin_Length]
      grind
    apply Eq.symm
    split_ifs with h_i h_eq h_1
    ·
      grind
    ·
      grind
    ·
      simp at h_i
      have h_i := LeSub.of.Le_Add h_i
      have h_i' := Lt.of.Le.Ne h_i (by simp_all [Ne.symm])
      have h_i'' := Sub.ge.One.of.Gt h_i'
      rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength (by simp_all) (by simp_all)]
      simp [EqMin.of.Lt h_sub]
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by linarith)]
      rw [GetAppend.eq.Get.of.GtLength]
      rw [GetSlice.eq.Get_Add.of.GtLengthSlice]
      ·
        grind
      ·
        rw [LengthSlice.eq.SubMin_Length]
        grind
    ·
      simp at h_i h_1 h_eq
      rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength]
      ·
        have h_i := LeSub.of.Le_Add h_i
        have h_i' := Lt.of.Le.Ne h_i (by simp_all [Ne.symm])
        have h_i'' := Sub.ge.One.of.Gt h_i'
        simp [EqMin.of.Lt h_sub]
        rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
        ·
          rw [GetAppend.eq.Get_Sub_Length.of.GtLengthAppend.GeLength] <;>
          ·
            simp [LengthSlice.eq.SubMin_Length]
            grind
        ·
          linarith
      ·
        simp_all
  ·
    simp at h_d
    subst h_d
    simp [Slice.eq.Nil]
    grind


-- created on 2025-06-21
-- updated on 2026-11-07
