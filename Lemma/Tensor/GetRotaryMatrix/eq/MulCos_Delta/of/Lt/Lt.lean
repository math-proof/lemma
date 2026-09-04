import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetMulEye_Stack.eq.MulDelta
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
open Tensor


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (i j : Fin (d + d))
  (hi : i < d)
  (hj : j < d) :
-- imply
  (rotaryMatrix θ)[i][j] = θ.cos[j]'(by grind) * (KroneckerDelta (α := Fin d) ⟨i, by grind⟩ ⟨j, by grind⟩ : Tensor ℝ []) := by
-- proof
  unfold rotaryMatrix
  extract_lets I
  let C := I * [_ < d] θ.cos
  let S := I * [_ < d] θ.sin
  apply (congrArg (fun t => t[j]) (GetAppend.eq.Get.of.Lt hi (C.hstack (-S)) (S.hstack C))).trans
  apply (GetHstack.eq.Get.of.Lt hj C (-S) ⟨i, by grind⟩).trans
  apply (GetMulEye_Stack.eq.MulDelta θ.cos ⟨i, by grind⟩ ⟨j, by grind⟩).trans
  apply Eq.trans (Tensor.Mul _ _)
  apply Eq.trans (Tensor.Mul.comm _ _)
  apply (Tensor.Mul _ _).symm


-- created on 2026-09-04
