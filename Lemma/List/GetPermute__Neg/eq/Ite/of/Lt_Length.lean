import Lemma.List.Permute.eq.Ite
import Lemma.List.GetAppend.eq.Get.of.Lt_Length
import Lemma.List.GetTake.eq.Get.of.Lt_LengthTake
import Lemma.List.LengthTake.eq.Min_Length
import Lemma.Algebra.EqMin.of.Lt
import Lemma.List.GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Nat.Add
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Algebra.AddAdd.eq.Add_Add
import Lemma.Nat.EqSubAdd
import Lemma.List.LengthAppend.eq.AddLengthS
import Lemma.List.LengthCons.eq.Add1Length
import Lemma.List.Slice.eq.Nil
import Lemma.List.LengthDrop.eq.SubLength
import Lemma.Algebra.LeAdd_1
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.Algebra.SubSub
import Lemma.List.GetSlice.eq.Get_Add.of.Lt_LengthSlice
import Lemma.Algebra.LeSub.is.Le_Add
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Algebra.Sub.ge.One.of.Gt
import Lemma.Algebra.LtSubS.of.Lt.Le
import Lemma.Algebra.LtSub_1.of.Le.Gt_0
import Lemma.Algebra.Le_Sub_1.of.Lt
import Lemma.Algebra.Lt.of.Le.Lt
import Lemma.Algebra.LeSub.of.Le
import Lemma.Nat.Eq.of.Le.Le
import Lemma.Algebra.EqAdd_Sub.of.Ge
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.SubAdd.eq.Sub_Sub.of.Ge
import Lemma.Algebra.AddAdd
import Lemma.Algebra.SubAdd.eq.AddSub.of.Le
import Lemma.Algebra.GeSub_1.of.Gt
import Lemma.Algebra.LtSub
import Lemma.List.LengthPermute.eq.Length
open Algebra List Nat


@[main]
private lemma MAIN
  {a : List α}
  {i : Fin a.length}
  {d t : ℕ}
-- given
  (h : t < a.length) :
-- imply
  have : t < (a.permute i (-d)).length := by rwa [LengthPermute.eq.Length]
  (a.permute i (-d))[t] =
    if t < i - d then
      a[t]
    else if t = i - d then
      a[i]
    else if t ≤ i then
      a[t - 1]
    else
      a[t] := by
-- proof
  have h_sub := LtSub i d
  simp [Permute.eq.Ite]
  split_ifs with h_d
  ·
    have h_t : t < (a.take (i - d)).length + (a[(i : ℕ)] :: (a.slice (i - d) i ++ a.drop (i + 1))).length := by
      rw [LengthCons.eq.Add1Length]
      rw [LengthAppend.eq.AddLengthS]
      rw [LengthDrop.eq.SubLength]
      rw [LengthSlice.eq.SubMin]
      rw [LengthTake.eq.Min_Length]
      repeat rw [EqMin.of.Lt (by simp_all)]
      repeat rw [Add_Add.eq.AddAdd]
      rw [Add.comm]
      rw [Add_Sub.eq.SubAdd.of.Ge (by simp_all)]
      rw [AddAdd.eq.Add_Add]
      rw [Add.comm (a := 1)]
      rw [EqSubAdd.left]
      rwa [EqAddSub.of.Ge (LeAdd_1 i)]
    apply Eq.symm
    split_ifs with h_i h_eq h_1
    ·
      rw [GetAppend.eq.Get.of.Lt_Length]
      rw [GetTake.eq.Get.of.Lt_LengthTake]
      simp_all [EqMin.of.Lt]
    ·
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp_all) (by simp_all)]
      simp_all [EqMin.of.Lt]
    ·
      simp at h_i
      have h_i := LeSub.of.Le_Add.nat h_i
      have h_i' := Lt.of.Le.Ne (by simp_all [Ne.symm]) h_i
      have h_i'' := Sub.ge.One.of.Gt h_i'
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength (by simp_all) (by simp_all)]
      simp [EqMin.of.Lt h_sub]
      rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0 (by linarith)]
      rw [GetAppend.eq.Get.of.Lt_Length]
      rw [GetSlice.eq.Get_Add.of.Lt_LengthSlice]
      ·
        simp [Add_Sub.eq.SubAdd.of.Ge h_i'']
        simp [Add_Sub.eq.SubAdd.of.Ge h_i]
      ·
        rw [LengthSlice.eq.SubMin]
        rw [SubSub.comm.nat]
        apply LtSubS.of.Lt.Le
        ·
          apply Le_Sub_1.of.Lt h_i'
        ·
          apply LtSub_1.of.Le.Gt_0.left (by linarith) (by simp_all)
    ·
      simp at h_i h_1 h_eq
      rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
      ·
        have h_i := LeSub.of.Le_Add.nat h_i
        have h_i' := Lt.of.Le.Ne (by simp_all [Ne.symm]) h_i
        have h_i'' := Sub.ge.One.of.Gt h_i'
        simp [EqMin.of.Lt h_sub]
        rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
        ·
          rw [GetAppend.eq.Get_Sub_Length.of.Lt_LengthAppend.GeLength]
          ·
            simp [LengthSlice.eq.SubMin]
            congr
            rw [Sub_Sub.eq.SubAdd.of.Ge]
            ·
              rw [Add.comm]
              rw [Add_Add.eq.AddAdd]
              rw [EqAddSub.of.Ge]
              ·
                rw [AddAdd.comm]
                repeat rw [EqAddSub.of.Ge (by assumption)]
              ·
                rw [AddSub.eq.SubAdd.of.Le]
                ·
                  rw [EqAddSub.of.Ge]
                  ·
                    apply GeSub_1.of.Gt
                    assumption
                  ·
                    assumption
                ·
                  assumption
            ·
              simp_all
          ·
            rw [LengthSlice.eq.SubMin]
            simp [Add.comm]
            rw [Add_Sub.eq.SubAdd.of.Ge (by simp_all)]
            rw [EqAdd_Sub.of.Ge (by simp_all)]
            apply Le_Sub_1.of.Lt h_1
        ·
          linarith
      ·
        simp_all
  ·
    simp at h_d
    subst h_d
    simp [Slice.eq.Nil]
    intro h_it
    apply Eq.symm
    split_ifs
    .
      aesop
    .
      omega
    .
      rfl


-- created on 2025-06-21
