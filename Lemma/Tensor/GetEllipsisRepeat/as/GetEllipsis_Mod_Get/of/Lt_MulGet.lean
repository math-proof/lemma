import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Algebra.LtMod.of.Lt_Mul
import Lemma.Algebra.Gt_0
import Lemma.Tensor.GetEllipsisRepeat.as.GetEllipsis_Mod_Get.of.Lt_MulGet.Lt_Length
open Algebra Tensor


@[main]
private lemma main
  {dim : Fin s.length}
-- given
  (h_i : i < n * s[dim])
  (X : Tensor α s) :
-- imply
  (X.repeat n dim).getEllipsis ⟨dim, by simp⟩ ⟨i, by simp_all⟩ ≃ X.getEllipsis dim ⟨i % s[dim], LtMod.of.Lt_Mul h_i⟩ := by
-- proof
  apply GetEllipsisRepeat.as.GetEllipsis_Mod_Get.of.Lt_MulGet.Lt_Length _ h_i



-- created on 2025-10-05
