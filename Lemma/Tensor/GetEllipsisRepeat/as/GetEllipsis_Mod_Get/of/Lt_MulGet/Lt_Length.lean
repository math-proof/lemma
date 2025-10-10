import stdlib.SEq
import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Tensor.GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0
import Lemma.Tensor.ToVectorRepeat.as.Map_FunRepeatGet.of.Lt_Get_0.GtVal_0
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.Algebra.Gt_0.of.Gt
import Lemma.Algebra.Lt_Sub.of.LtAdd
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.LengthEraseIdx.eq.SubLength_1.of.Lt_Length
import Lemma.List.EqCons_Tail.of.GtLength_0
import Lemma.List.GetEraseIdx.eq.Get.of.Lt.Lt_Length
import Lemma.Tensor.ToVector.eq.MapRange_Get.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Algebra.EqSubAdd
import Lemma.List.EraseIdxSet.eq.EraseIdx
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Nat.LtVal
import Lemma.List.LengthSet.eq.Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Vector.EqGetRange
import Lemma.Tensor.GetEllipsisCast.eq.Cast_GetEllipsis.of.Eq
import Lemma.List.EqCons_Tail.of.Eq_Get_0.GtLength_0
import Lemma.Bool.SEqCast.of.Eq
open Algebra Tensor List Vector Bool Nat


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
    have h_tail : s.tail.length > 0 := by
      simp
      linarith
    have h_dim := Lt_Sub.of.LtAdd.nat h_dim
    have ih := ih (s := s.tail) (by simp [h_dim]) (by rwa [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 (by omega)])
    simp only [h_tail] at ih
    simp at ih
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by simpa) (by simp)]
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by simpa)]
      apply EqCons_Tail.of.Eq_Get_0.GtLength_0
      rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by simpa) (by simp)]
      simp
    ·
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by simpa)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      apply EqCons_Tail.of.Eq_Get_0.GtLength_0
      rw [GetEraseIdx.eq.Get.of.Lt.Lt_Length (by simpa) (by simp)]
    ·
      rw [ToVector.eq.MapRange_Get.of.GtLength_0 (by simpa)]
      simp
      apply SEq.of.All_SEqGetS.Eq.Eq
      ·
        rw [TailSet.eq.SetTail.of.Gt_0 (by simp)]
        rw [EqSubAdd.int]
        rw [EraseIdxSet.eq.EraseIdx]
      ·
        intro t
        repeat rw [GetFromVector.eq.Get]
        simp
        have h_t := LtVal t
        have h_fin := EqGetRange.fin (⟨t, by simp_all⟩ : Fin ((s.set (dim + 1) (n * s.get ⟨dim + 1, by simpa⟩)).headD 1))
        simp only [HeadD.eq.Get_0.of.GtLength_0 (show (s.set (dim + 1) (n * s[dim + 1])).length > 0 by rwa [LengthSet.eq.Length])] at h_t
        rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by simpa) (by simp)] at h_t
        have h_fin' := EqGetRange.fin (⟨t, by simp only [HeadD.eq.Get_0.of.GtLength_0 h_s]; assumption⟩ : Fin (s.headD 1))
        rw [← Length.eq.Get_0.of.GtLength_0 h_s X] at h_t
        have ih := ih X[t]
        simp only [GetElem.getElem] at ih ⊢
        simp only [h_fin', h_fin]
        apply SEq.symm ∘ SEq.of.SEq.SEq ih.symm
        rw [GetEllipsisCast.eq.Cast_GetEllipsis.of.Eq (by simp) ((X.get ⟨t, by assumption⟩).repeat n ⟨dim, by simpa⟩) ⟨dim, by simpa⟩ ⟨i, by simpa⟩]
        apply SEqCast.of.Eq
        simp
      ·
        repeat rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
        rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by simpa) (by simp)]


-- created on 2025-10-05
-- updated on 2025-10-07
