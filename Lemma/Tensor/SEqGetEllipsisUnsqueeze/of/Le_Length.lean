import stdlib.SEq
import sympy.tensor.tensor
import Lemma.List.LengthInsertIdx.eq.Add1Length.of.Le_Length
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.Tensor.ToVector.eq.MapRange_Get.of.GtLength_0
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq
import Lemma.Tensor.GetFromVector.eq.Get
import Lemma.Vector.EqGetRange
import Lemma.Tensor.GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0
open List Tensor Vector


@[main]
private lemma main
-- given
  (h_dim : dim ≤ s.length)
  (X : Tensor α s) :
-- imply
  (X.unsqueeze dim).select ⟨dim, by rw [LengthInsertIdx.eq.Add1Length.of.Le_Length h_dim]; omega⟩ ⟨0, by simp⟩ ≃ X := by
-- proof
  induction dim generalizing s X with
  | zero =>
    unfold Tensor.select
    have := EqGetUnsqueeze.fin X
    simp at this ⊢
    rw [this]
  | succ dim ih =>
    match s with
    | [] =>
      contradiction
    | s₀ :: s =>
      unfold Tensor.select
      simp
      rw [ToVector.eq.MapRange_Get.of.GtLength_0]
      ·
        simp
        apply SEq.of.All_SEqGetS.Eq
        ·
          simp
        ·
          intro i
          rw [GetFromVector.eq.Get]
          simp
          have h := GetUnsqueeze.eq.Cast_UnsqueezeGet.of.Lt_Get_0.Gt_0.GtLength_0.fin (by simp) (by simp) (by simp) X (s := s₀ :: s) (d := dim + 1) (i := (List.Vector.range s₀)[i])
          simp at h
          rw [h]
          simp at h_dim
          have ih := ih h_dim (X.get (List.Vector.range s₀)[i])
          apply SEq.trans ih
          simp [GetElem.getElem]
          rw [EqGetRange.fin]
      ·
        simp


-- created on 2025-10-07
