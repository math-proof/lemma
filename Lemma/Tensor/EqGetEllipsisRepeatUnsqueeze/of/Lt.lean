import sympy.tensor.tensor
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Algebra.EqMod_1'0
import Lemma.Tensor.EqGetUnsqueeze
import Lemma.List.Lt_LengthInsertIdx
open Tensor Algebra List


@[main]
private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α s)
  (dim : Fin s.length) :
-- imply
  have h_dim := Lt_LengthInsertIdx dim 1
  ((X.unsqueeze dim).repeat n ⟨dim, h_dim⟩).getEllipsis ⟨dim, by simp_all⟩ ⟨i, by simp_all⟩ ≃ X := by
-- proof
  sorry


-- created on 2025-10-05
