import Lemma.Tensor.EqGetUnsqueeze_0
import Lemma.Tensor.GetOfVector.eq.Get
import Lemma.Tensor.GetUnsqueeze.as.UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq
import Lemma.Tensor.Select.as.OfVectorMapToVector.of.GtVal_0
import Lemma.Tensor.Select_0.as.Get.of.GtLength_0
import Lemma.Tensor.ToVector.eq.MapRange_Get.of.GtLength_0
import Lemma.Vector.GetMap.eq.UFnGet
import Lemma.Bool.SEq.is.SEqCast.of.Eq
open Tensor Vector Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.SEqSelectUnsqueeze.of.GeLength |
| cast | Tensor.SelectUnsqueeze.eq.Cast.of.GeLength |
-/
@[main, cast]
private lemma main
-- given
  (h_dim : s.length ≥ d)
  (X : Tensor α s) :
-- imply
  (X.unsqueeze d).select ⟨d, by rw [List.LengthInsertIdx.eq.Add1Length.of.GeLength h_dim]; omega⟩ ⟨0, by simp⟩ ≃ X := by
-- proof
  induction d generalizing s X with
  | zero =>
    rw [Select_0.eq.Cast_Get.of.GtLength_0]
    have := EqGetUnsqueeze_0.fin X
    simp at this ⊢
    rw [this]
    rfl
  | succ d ih =>
    match s with
    | [] =>
      contradiction
    | s₀ :: s =>
      rw [Select.eq.Cast_OfVectorMapToVector.of.GtVal_0 (by grind) (i := ⟨0, by grind⟩)]
      simp
      apply SEqCast.of.SEq.Eq (by grind)
      erw [ToVector.eq.MapRange_Get.of.GtLength_0]
      ·
        simp
        apply SEq.of.All_SEqGetS.Eq
        ·
          simp
        ·
          intro i
          rw [GetOfVector.eq.Get]
          simp only [GetElem.getElem]
          have h := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.GtGet_0.Gt_0.GtLength_0.fin (by simp) (by simp) (by simp) X (s := s₀ :: s) (d := d + 1) (i := (List.Vector.range s₀)[i])
          simp at h
          rw [GetMap.eq.UFnGet.fin]
          erw [GetMap.eq.UFnGet.fin]
          erw [h]
          simp at h_dim
          have ih := ih h_dim (X.get (List.Vector.range s₀)[i])
          apply ih.trans
          simp [GetElem.getElem]
          rw [Vector.EqGetRange.fin]
          rfl
      ·
        simp


-- created on 2025-10-07
-- updated on 2026-07-24
