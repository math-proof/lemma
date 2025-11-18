import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Nat.Gt_0
import Lemma.Tensor.SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet.Lt_Length
open Tensor Nat


@[main]
private lemma main
  {d : Fin s.length}
-- given
  (h_i : i < n * s[d])
  (X : Tensor α s) :
-- imply
  (X.repeat n d).select ⟨d, by simp⟩ ⟨i, by simp_all⟩ ≃ X.select d ⟨i % s[d], LtMod.of.Lt_Mul h_i⟩ := by
-- proof
  apply SelectRepeat.as.Select_Mod_Get.of.Lt_MulGet.Lt_Length _ h_i



-- created on 2025-10-05
