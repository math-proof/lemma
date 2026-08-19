import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Bool.SEq.of.SEq.SEq
import Lemma.Bool.SEqCastS.of.SEq.Eq.Eq
import Lemma.List.EqCons_Tail.of.Eq_Get_0.GtLength_0
import Lemma.List.EraseIdxSet.eq.EraseIdx
import Lemma.List.EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1
import Lemma.List.GetEraseIdx.eq.Get.of.Gt.GtLength
import Lemma.List.GetSet.eq.Get_0.of.Gt_0.GtLength_0
import Lemma.List.GetTail.eq.Get_Add_1.of.Lt_SubLength_1
import Lemma.List.HeadD.eq.Get_0.of.GtLength_0
import Lemma.List.HeadDSet.eq.Get_0.of.Gt_0.LtLength
import Lemma.List.TailSet.eq.SetTail.of.Gt_0
import Lemma.Nat.EqSubAdd
import Lemma.Nat.Gt_0.of.Gt
import Lemma.Nat.Lt_Sub.of.LtAdd
import Lemma.Tensor.GetOfVector.eq.Get
import Lemma.Tensor.GetResize_0.as.Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.SEqResizeS.of.SEq.Val.Eq
import Lemma.Tensor.SEqSelectS.of.SEq
import Lemma.Tensor.Select.as.OfVectorMapToVector.of.GtVal_0
import Lemma.Tensor.SelectCast.as.Select.of.Eq
import Lemma.Tensor.Select_0.as.Get.of.GtGet_0.GtLength_0
import Lemma.Tensor.ToVector.eq.MapRange_Get.of.GtLength_0
import Lemma.Tensor.ToVectorResize.as.Map_FunResizeGet.of.GtGet_0.GtVal_0
import Lemma.Vector.EqGetRange
open Bool List Nat Tensor Vector


@[main]
private lemma main
  [Zero α]
  {d i n : ℕ}
-- given
  (h_d : s.length > d)
  (h_i : i < s[d])
  (X : Tensor α s) :
-- imply
  (X.resize ⟨d, h_d⟩ (s[d] ⊔ n)).select ⟨d, by simp_all⟩ ⟨i, by aesop⟩ ≃ X.select ⟨d, h_d⟩ ⟨i, by grind⟩ := by
-- proof
  have h_s := Gt_0.of.Gt h_d
  induction d generalizing X s with
  | zero =>
    apply SEq.of.SEq.SEq (Select_0.as.Get.of.GtGet_0.GtLength_0 (by simpa) (by grind) (X.resize ⟨0, h_s⟩ (s[0] ⊔ n)) (i := i))
    apply SEq.of.SEq.SEq (Select_0.as.Get.of.GtGet_0.GtLength_0 (by simpa) (by grind) X (i := i))
    simp only [GetElem.getElem]
    apply GetResize_0.as.Get.of.GtLength_0.fin (i := ⟨i, by grind⟩)
  | succ d ih =>
    rw [Select.eq.Cast_OfVectorMapToVector.of.GtVal_0 (by grind)]
    conv_rhs => rw [Select.eq.Cast_OfVectorMapToVector.of.GtVal_0 (by grind)]
    simp
    apply SEqCastS.of.SEq.Eq.Eq
    ·
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by simpa) (by simp)]
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by grind)]
      apply EqCons_Tail.of.Eq_Get_0.GtLength_0
      rw [GetEraseIdx.eq.Get.of.Gt.GtLength (by simpa) (by simp)]
      simp
    ·
      rw [EraseIdxTail.eq.TailEraseIdx.of.Lt_SubLength_1 (by grind)]
      rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
      apply EqCons_Tail.of.Eq_Get_0.GtLength_0
      rw [GetEraseIdx.eq.Get.of.Gt.GtLength (by simpa) (by simp)]
    ·
      rw [ToVectorResize.as.Map_FunResizeGet.of.GtGet_0.GtVal_0 (by simp)]
      simp
      have h_d := Lt_Sub.of.LtAdd h_d
      have ih := ih (s := s.tail) (by simp [h_d]) (by rwa [GetTail.eq.Get_Add_1.of.Lt_SubLength_1 (by omega)])
      simp only [show s.tail.length > 0 by grind] at ih
      simp at ih
      ·
        rw [ToVector.eq.MapRange_Get.of.GtLength_0 (by simpa)]
        simp
        apply SEq.of.All_SEqGetS.Eq.Eq
        ·
          rw [TailSet.eq.SetTail.of.Gt_0 (by simp)]
          rw [EqSubAdd]
          rw [EraseIdxSet.eq.EraseIdx]
        ·
          intro t
          repeat rw [GetOfVector.eq.Get]
          simp
          have h_t := t.isLt
          simp only [HeadDSet.eq.Get_0.of.Gt_0.LtLength (s := s) (d := d + 1) (by grind) (by grind)] at h_t
          have h_fin := EqGetRange.fin (⟨t, by simpa only [HeadDSet.eq.Get_0.of.Gt_0.LtLength (s := s) (d := d + 1) (by grind) (by grind)]⟩ : Fin ((s.set (d + 1) (s.get ⟨d + 1, by grind⟩ ⊔ n)).headD 1))
          have h_fin' := EqGetRange.fin (⟨t, by simp only [HeadD.eq.Get_0.of.GtLength_0 h_s]; assumption⟩ : Fin (s.headD 1))
          rw [← Length.eq.Get_0.of.GtLength_0 h_s X] at h_t
          have ih := ih X[t]
          simp only [GetElem.getElem] at ih ⊢
          simp only [h_fin', h_fin]
          apply SEq.symm ∘ SEq.of.SEq.SEq ih.symm
          erw [SelectCast.eq.Cast_Select.of.Eq (by simp) ((X.get ⟨t, by assumption⟩).resize ⟨d, by simpa⟩ ((s.get ⟨d + 1, by grind⟩ ⊔ n))) ⟨d, by simpa⟩ ⟨i, by simp; grind⟩]
          apply SEqCast.of.SEq.Eq (by simp)
          simp
          apply SEqSelectS.of.SEq
          apply SEqResizeS.of.SEq.Val.Eq (by simp) (by simp)
          rfl
        ·
          repeat rw [HeadD.eq.Get_0.of.GtLength_0 (by simpa)]
          rw [GetSet.eq.Get_0.of.Gt_0.GtLength_0 (by simpa) (by simp)]


-- created on 2026-07-30
