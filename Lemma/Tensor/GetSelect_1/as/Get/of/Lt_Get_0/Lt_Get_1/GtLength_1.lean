import Lemma.Tensor.GetSelect_1.as.Get.of.Lt.Lt_Get_0.GtLength_0
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import Lemma.Tensor.LengthGet.eq.Get_0.of.Lt_Get_0.GtLength_1
import Lemma.Tensor.LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0
import stdlib.SEq
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
-- given
  (h_s : s.length > 1)
  (h_i : i < s[1])
  (h_j : j < s[0])
  (X : Tensor α s) :
-- imply
  (X.select ⟨1, by grind⟩ ⟨i, by grind⟩).get ⟨j, by simp [LengthSelect.eq.Get_0.of.Lt_Get.GtLength.Gt_0]; grind⟩ ≃ (X.get ⟨j, by rwa [Length.eq.Get_0.of.GtLength_0]⟩).get ⟨i, by simp_all [LengthGet.eq.Get_0.of.Lt_Get_0.GtLength_1]⟩ := by
-- proof
  match s with
  | [] =>
    contradiction
  | n :: s =>
    apply GetSelect_1.as.Get.of.Lt.Lt_Get_0.GtLength_0
    repeat grind


-- created on 2025-11-14
