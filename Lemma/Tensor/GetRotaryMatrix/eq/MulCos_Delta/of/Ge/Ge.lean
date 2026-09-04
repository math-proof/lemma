import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetMulEye_Stack.eq.MulDelta
import Lemma.Tensor.Mul
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import sympy.functions.special.tensor_functions
import sympy.matrices.expressions.special
import sympy.tensor.functions
open Tensor


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (i j : Fin (d + d))
  (hi : i ≥ d)
  (hj : j ≥ d) :
-- imply
  (rotaryMatrix θ)[i][j] = θ.cos[j - d]'(by grind) * (KroneckerDelta (α := Fin d) ⟨i - d, by grind⟩ ⟨j - d, by grind⟩ : Tensor ℝ []) := by
-- proof
  unfold rotaryMatrix
  extract_lets I
  let C := I * [_ < d] θ.cos
  let S := I * [_ < d] θ.sin
  apply (congrArg (fun t => t[j]) (GetAppend.eq.Get_Sub.of.GtAdd.Ge hi i.isLt (C.hstack (-S)) (S.hstack C))).trans
  apply (GetHstack.eq.Get_Sub.of.GtAdd.Ge hj j.isLt S C ⟨i - d, by grind⟩).trans
  apply (GetMulEye_Stack.eq.MulDelta θ.cos ⟨i - d, by grind⟩ ⟨j - d, by grind⟩).trans
  apply Eq.trans (Tensor.Mul _ _)
  apply Eq.trans (Tensor.Mul.comm _ _)
  apply (Tensor.Mul _ _).symm


-- created on 2026-09-04
