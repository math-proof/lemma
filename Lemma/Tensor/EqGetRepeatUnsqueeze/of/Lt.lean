import sympy.tensor.tensor
import Lemma.Tensor.LengthRepeat.eq.MulGet_0.of.GtLength_0
import Lemma.Tensor.GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0
import Lemma.Algebra.EqMod_1'0
import Lemma.Tensor.EqGetUnsqueeze_0_0
open Tensor Algebra


@[main]
private lemma main
-- given
  (h_i : i < n)
  (X : Tensor α s) :
-- imply
  have : i < ((X.unsqueeze 0).repeat n ⟨0, by simp⟩).length := by
    rw [LengthRepeat.eq.MulGet_0.of.GtLength_0]
    simpa
  ((X.unsqueeze 0).repeat n ⟨0, by simp⟩)[i] = X := by
-- proof
  intro h_i'
  rw [GetRepeat.eq.Cast_Get_Mod_Get.of.Lt_Mul_Get.GtLength_0]
  ·
    simp [EqMod_1'0]
    apply EqGetUnsqueeze_0_0
  ·
    simpa


@[main]
private lemma fin
-- given
  (h_i : i < n)
  (X : Tensor α s) :
-- imply
  have h_i : i < ((X.unsqueeze 0).repeat n ⟨0, by simp⟩).length := by
    rw [LengthRepeat.eq.MulGet_0.of.GtLength_0]
    simpa
  ((X.unsqueeze 0).repeat n ⟨0, by simp⟩).get ⟨i, h_i⟩ = X := by
-- proof
  apply main
  assumption


-- created on 2025-07-10
-- updated on 2025-07-11
