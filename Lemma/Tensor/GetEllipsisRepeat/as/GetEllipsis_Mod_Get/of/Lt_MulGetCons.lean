import stdlib.SEq
import Mathlib.Data.Vector.MapLemmas
import Lemma.Algebra.LtMod.of.Lt_Mul
import Lemma.Tensor.GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0
import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0
import Lemma.Tensor.ToVectorRepeat.as.Map_FunRepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.Logic.SEqCastS.of.SEq.Eq.Eq
import Lemma.Algebra.Gt_0.of.Gt
import Lemma.Algebra.Lt_Sub.of.LtAdd
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.List.GetSet.eq.Get.of.Gt.Lt_Length
open Algebra Tensor Logic List


@[main]
private lemma main
-- given
  (h_dim : dim < s.length)
  (h_i : i < n * s[dim])
  (X : Tensor α s) :
-- imply
  (X.repeat n ⟨dim, h_dim⟩).getEllipsis ⟨dim, by simp_all⟩ ⟨i, by aesop⟩ ≃ X.getEllipsis ⟨dim, h_dim⟩ ⟨i % s[dim], LtMod.of.Lt_Mul h_i⟩ := by
-- proof
  have h_s := Gt_0.of.Gt h_dim
  induction dim generalizing X s with
  | zero =>
    have h := GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0 (by simpa) (by simpa) (X.repeat n ⟨0, h_s⟩)
    apply SEq.of.SEq.SEq h
    have h := GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0 (by simpa) (by simp [LtMod.of.Lt_Mul h_i]) X (i := i % s[0])
    apply SEq.of.SEq.SEq h
    apply GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0.fin
    assumption
  | succ dim ih =>
    unfold Tensor.getEllipsis
    simp
    rw [ToVectorRepeat.as.Map_FunRepeatGet.of.Lt_Get_0.GtVal_0 (by simp)]
    simp
    have h_s : s.tail.length > 0 := by
      simp
      linarith
    have h_dim := Lt_Sub.of.LtAdd.nat h_dim
    have ih := ih (s := s.tail) (by simp [h_dim]) (by rwa [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 (by omega)])
    simp only [h_s] at ih
    simp at ih
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by simpa) (by simp)]
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by simpa)]
      have h_length : ((s.set (dim + 1) (n * s[dim + 1])).eraseIdx (dim + 1)).length > 0 := by
        rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by simpa)]
        simp_all
      conv_rhs =>
        rw [Eq_Cons_Tail.of.GtLength_0 h_length]
      simp
      rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by simpa) (by simp)]
      rw [GetSet.eq.Get.of.Gt.Lt_Length]
      simp
    ·
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by simpa)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      have h_length : (s.eraseIdx (dim + 1)).length > 0 := by
        rw [LengthEraseIdx.eq.SubLength_1.of.Lt_Length (by simpa)]
        simp_all
      conv_rhs =>
        rw [Eq_Cons_Tail.of.GtLength_0 h_length]
      simp
      rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by simpa) (by simp)]
    ·
      sorry


-- created on 2025-10-05
-- updated on 2025-10-06
