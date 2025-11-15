import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
import Lemma.Tensor.SEqGetS.of.SEq.Lt_Length
import Lemma.Tensor.Select.as.Stack_Select.of.LtAdd_1Length
import sympy.tensor.tensor
open Tensor


@[main, comm]
private lemma main
-- given
  (h_d : d + 1 < s.length)
  (h_i : i < s[d + 1])
  (h_j : j < s[0])
  (X : Tensor α s) :
-- imply
  have h_length := Length.eq.Get_0.of.GtLength_0 (by omega) X
  (X.select ⟨d + 1, h_d⟩ ⟨i, by simpa⟩).get ⟨j, by rw [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0 (by simp) (by simpa) (by simpa)]; simpa⟩ ≃ (X.get ⟨j, by simpa [h_length]⟩).select ⟨d, by grind⟩ ⟨i, by simpa⟩ := by
-- proof
  intro h_length
  have := Select.as.Stack_Select.of.LtAdd_1Length h_d X ⟨i, h_i⟩
  have h_i' : j < (X.select ⟨d + 1, h_d⟩ ⟨i, by simpa⟩).length := by
    rwa [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0 (by linarith)]
  have := SEqGetS.of.SEq.Lt_Length.fin h_i' this
  rwa [EqGetStack.fn.fin] at this


-- created on 2025-11-07
-- updated on 2025-11-15
