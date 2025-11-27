import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetS.of.Eq.GtLength_0
import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.Lt_Get_0.GtLength_0
import Lemma.Tensor.GetSum.eq.Sum_Get.of.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSum.eq.Get_0.of.GtLength_0
import Lemma.Tensor.SEq0S.of.Eq
import Lemma.Tensor.SEqSumS.of.All_SEq.Gt_0
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Tensor.Sum_0.eq.Sum_Get
open Tensor
set_option maxHeartbeats 1000000


@[main, comm]
private lemma main
  [AddCommMonoid α]
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α (s₀ :: s)) :
-- imply
  have h_Xi : i < (X.sum 0).length := by rwa [LengthSum.eq.Get_0.of.GtLength_0 h_s]
  (X.sum 0).get ⟨i, h_Xi⟩ ≃ (X.select ⟨1, by grind⟩ ⟨i, by grind⟩).sum 0 := by
-- proof
  intro h_Xi
  if h₀ : s₀ = 0 then
    subst h₀
    simp [Sum.eq.Zero]
    have := Sum.eq.Zero X
    rw [EqGetS.of.Eq.GtLength_0 h_s this ⟨i, h_i⟩]
    rw [EqGet0_0.fin]
    apply SEq0S.of.Eq
    simp
  else
    have h_sum := Sum_0.eq.Sum_Get.fin X
    have h_sum : (X.sum 0).get ⟨i, h_Xi⟩ = (∑ i : Fin s₀, X.get i).get ⟨i, by simpa [← h_sum]⟩ := by
      congr
      simp
      aesop
    simp [Sum_0.eq.Sum_Get.fin]
    simp [h_sum]
    have h_all : ∀ k : Fin s₀, (X.select ⟨1, by grind⟩ ⟨i, by grind⟩).get k ≃ (X.get ⟨k, by rw [Length.eq.Get_0.of.GtLength_0 (by simp)]; simp⟩).get ⟨i, by rw [Length.eq.Get_0.of.GtLength_0 (by simpa)]; simpa⟩ := by
      intro k
      apply GetSelect_1.as.Get.of.Lt.Lt_Get_0.GtLength_0 h_s h_i
      simp
    have := SEqSumS.of.All_SEq.Gt_0 (by omega) h_all
    simp at this
    apply SEq.symm ∘ SEq.trans this
    rw [GetSum.eq.Sum_Get.of.GtLength_0 h_s (fun i : Fin s₀ => X.get i) ⟨i, by omega⟩]


-- created on 2025-11-01
-- updated on 2025-11-06
