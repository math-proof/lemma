import Lemma.Tensor.CosNeg.eq.Cos
import Lemma.Tensor.NegMul_Stack.eq.Mul_Stack_Neg
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.SinNeg.eq.NegSin
import Lemma.Tensor.TAppendHstackS.eq.AppendHstackSTS
import Lemma.Tensor.TMulEye.eq.MulEye
open Tensor


@[main]
private lemma main
-- given
  (α : Tensor ℝ [d]) :
-- imply
  rotaryMatrix (-α) = (rotaryMatrix α)ᵀ := by
-- proof
  simp [RotaryMatrix.eq.AppendHstackSMulSEye]
  rw [CosNeg.eq.Cos, SinNeg.eq.NegSin]
  rw [Mul_Stack_Neg.eq.NegMul_Stack]
  rw [neg_neg]
  conv_rhs =>
    rw [NegMul_Stack.eq.Mul_Stack_Neg]
    rw [TAppendHstackS.eq.AppendHstackSTS]
    rw [TMulEye.eq.MulEye α.cos, TMulEye.eq.MulEye α.sin, TMulEye.eq.MulEye (-α.sin)]
    rw [Mul_Stack_Neg.eq.NegMul_Stack]


-- created on 2026-09-03
