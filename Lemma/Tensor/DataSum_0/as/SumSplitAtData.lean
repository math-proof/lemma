import Lemma.Bool.SEq.is.SEqCast.of.Eq
import Lemma.Tensor.DataSum_0.eq.SumSplitAtData
import Lemma.Vector.SEq.of.All_EqGetS.Eq
import Lemma.Vector.HeadMap.eq.UFnHead
open Bool Tensor Vector


@[main, comm, cast]
private lemma main
  [Add α] [Zero α]
-- given
  (X : Tensor α s) :
-- imply
  (X.sum 0).data ≃ (X.data.splitAt 1).sum := by
-- proof
  match s with
  | .nil =>
    unfold Tensor.sum
    simp
    apply SEqCast.of.SEq.Eq (by simp)
    apply SEq.of.All_EqGetS.Eq.fin
    ·
      intro t
      have h_t := t.isLt
      conv_rhs at h_t => simp
      fin_cases t
      simp
      erw [GetFlatten.eq.Get.of.Eq_AddMul.fin (i := ⟨0, by grind⟩) (j := ⟨0, by grind⟩) (by grind)]
      simp
      congr
      erw [HeadMap.eq.UFnHead]
      erw [EqHeadSplitAt_0]
      rfl
    ·
      simp
  | s₀ :: s =>
    rw [DataSum_0.eq.SumSplitAtData]
    rfl


-- created on 2026-07-22
