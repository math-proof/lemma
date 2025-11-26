import Lemma.Tensor.GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
open Tensor


@[main]
private lemma main
-- given
  (h_d : d < s.length)
  (h_d₀ : d > 0)
  (h_i : i < s[d])
  (h_j : j < s[0])
  (X : Tensor α s) :
-- imply
  have h_length := Length.eq.Get_0.of.GtLength_0 (by omega) X
  (X.select ⟨d, h_d⟩ ⟨i, by simpa⟩).get ⟨j, by rw [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0 h_d₀ (by simpa) (by simpa)]; simpa⟩ ≃ (X.get ⟨j, by simpa [h_length]⟩).select ⟨d - 1, by grind⟩ ⟨i, by grind⟩ := by
-- proof
  intro h_shape
  cases d with
  | zero =>
    contradiction
  | succ d =>
    apply GetSelect.as.SelectGet.of.Lt_Get_0.Lt_Get_Add_1.LtAdd_1Length h_d h_i h_j


-- created on 2025-11-15
