import Lemma.Tensor.EqGetS.of.Eq.Lt
import Lemma.Tensor.LengthSum.eq.Get_0.of.GtLength_0
import Lemma.Tensor.Sum_0.eq.Sum_Get
import stdlib.SEq
open Tensor


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (h_s : s.length > 0)
  (h_i : i < s[0])
  (X : Tensor α (s₀ :: s)) :
-- imply
  have h_Xi : i < (X.sum 0).length := by rwa [LengthSum.eq.Get_0.of.GtLength_0 h_s]
  (X.sum 0).get ⟨i, h_Xi⟩ ≃ (X.getEllipsis ⟨1, by grind⟩ ⟨i, by grind⟩).sum 0 := by
-- proof
  intro h_Xi
  have h_sum := Sum_0.eq.Sum_Get.fin X
  have h_sum : (X.sum 0).get ⟨i, h_Xi⟩ = (∑ i : Fin s₀, X.get i).get ⟨i, by simpa [← h_sum]⟩ := by
    congr
    simp
    aesop
  simp [Sum_0.eq.Sum_Get.fin]
  simp [h_sum]
  sorry


-- created on 2025-11-01
