import sympy.tensor.tensor
import Lemma.Tensor.LengthRepeat.eq.MulGet_0.of.GtLength_0
import Lemma.Tensor.GetRepeat_0.as.Get_Mod_Get.of.GtMul_Get.GtLength_0
import Lemma.Nat.EqMod_1'0
import Lemma.Tensor.EqGetUnsqueeze_0
open Tensor Nat


@[main, fin]
private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α s) :
-- imply
  have : i < ((X.unsqueeze 0).repeat ⟨0, by simp⟩ n).length := by
    rw [LengthRepeat.eq.MulGet_0.of.GtLength_0]
    simpa
  ((X.unsqueeze 0).repeat ⟨0, by simp⟩ n)[i] = X := by
-- proof
  intro h_i'
  rw [GetRepeat_0.eq.Cast_Get_Mod_Get.of.GtMul_Get.GtLength_0]
  ·
    simp [EqMod_1'0]
    apply EqGetUnsqueeze_0
  ·
    simpa


-- created on 2025-07-10
-- updated on 2025-07-11
