import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Nat.Gt_0
import Lemma.Tensor.SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet.Lt_Length
open Tensor Nat


@[main]
private lemma main
  {dim : Fin s.length}
-- given
  (h_i : i < n * s[dim])
  (X : Tensor α s) :
-- imply
  (X.repeat n dim).select ⟨dim, by simp⟩ ⟨i, by simp_all⟩ ≃ X.select dim ⟨i % s[dim], LtMod.of.Lt_Mul h_i⟩ := by
-- proof
  apply SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet.Lt_Length _ h_i



-- created on 2025-10-05
