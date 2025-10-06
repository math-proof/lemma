import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Algebra.LtMod.of.Lt_Mul
import Lemma.Tensor.GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0
import Lemma.Logic.SEq.of.SEq.SEq
import Lemma.Tensor.GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0
open Algebra Tensor Logic


@[main]
private lemma main
  {dim : Fin (s.length + 1)}
-- given
  (h_i : i < n * (s₀ :: s)[dim])
  (X : Tensor α (s₀ :: s)) :
-- imply
  (X.repeat n dim).getEllipsis ⟨dim, by simp⟩ ⟨i, by simp_all⟩ ≃ X.getEllipsis dim ⟨i % (s₀ :: s)[dim], LtMod.of.Lt_Mul h_i⟩ := by
-- proof
  induction dim using Fin.inductionOn generalizing X with
  | zero =>
    have h := GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0 (by simp) h_i (X.repeat n ⟨0, by simp⟩)
    apply SEq.of.SEq.SEq h
    simp at h_i
    have h := GetEllipsis_0.as.Get.of.Gt_Length_0.Lt_Get_0 (by simp) (by simp [LtMod.of.Lt_Mul h_i]) X (i := i % s₀)
    apply SEq.of.SEq.SEq h
    apply GetRepeat.as.Get_Mod_Get.of.Lt_MulGet.GtLength_0.fin
    assumption
  | succ dim ih =>
    unfold Tensor.getEllipsis
    simp
    sorry


-- created on 2025-10-05
