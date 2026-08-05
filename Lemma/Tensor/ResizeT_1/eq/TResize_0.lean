import Lemma.Bool.SEq.is.Eq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.GetResize.as.ResizeGet.of.GtGet_0.GtVal_0
import Lemma.Tensor.GetSelect_1.as.Get.of.GtGet_0.GtGet_1.GtLength_1
import Lemma.Tensor.GetT.eq.Select
import Lemma.Tensor.SelectResize.as.ResizeSelect.of.Lt
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
open Bool Tensor List


@[main]
private lemma main
  [Zero α]
-- given
  (X : Tensor α [n, m])
  (k : ℕ) :
-- imply
  Xᵀ.resize ⟨1, by simp [EqSwap_0'1]⟩ k = (X.resize ⟨0, by grind⟩ k)ᵀ := by
-- proof
  apply Eq.of.SEq
  apply SEq.of.All_SEqGetS.Eq
  ·
    simp [List.set, List.slice, List.array_slice]
  ·
    intro i
    simp only [GetElem.getElem]
    conv_lhs => erw [GetResize.eq.Cast_ResizeGet.of.GtGet_0.GtVal_0.fin (by grind) (by simp [EqSwap_0'1]) (d := ⟨1, by simp [EqSwap_0'1]⟩)]
    conv_rhs => erw [GetT.eq.Select]
    simp
    apply SEqCast.of.SEq.Eq (by simp [EqSwap_0'1, List.slice, List.array_slice])
    apply SEq.of.All_SEqGetS.Eq
    ·
      simp
    ·
      intro j
      simp only [GetElem.getElem]
      conv_lhs => erw [GetT.eq.Select]
      apply SEqGetS.of.SEq.GtLength.fin (by grind) _ (i := j)
      apply ResizeSelect.as.SelectResize.of.Lt (d := ⟨1, by grind⟩) (by grind) X i k


-- created on 2026-07-30
