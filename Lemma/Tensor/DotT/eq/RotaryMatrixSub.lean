import Lemma.Tensor.AddMulS_Stack.eq.Mul_Stack_Add
import Lemma.Tensor.CosSub.eq.AddMulS
import Lemma.Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS
import Lemma.Tensor.DotMulSEye.eq.MulEye
import Lemma.Tensor.Mul_Neg.eq.NegMul
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Tensor.NegMul_Stack.eq.Mul_Stack_Neg
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.SinSub.eq.SubMulSSin_Cos
import Lemma.Tensor.TAppendHstackS.eq.AppendHstackSTS
import Lemma.Tensor.TMulEye.eq.MulEye
open Tensor


@[main]
private lemma main
-- given
  (α β : Tensor ℝ [d]) :
-- imply
  α.rotaryMatrixᵀ @ β.rotaryMatrix = (β - α).rotaryMatrix := by
-- proof
  conv_lhs =>
    arg 1
    simp only [rotaryMatrix]
    rw [NegMul_Stack.eq.Mul_Stack_Neg]
    rw [TAppendHstackS.eq.AppendHstackSTS]
    rw [TMulEye.eq.MulEye α.cos, TMulEye.eq.MulEye α.sin, TMulEye.eq.MulEye (-α.sin)]
    rw [Mul_Stack_Neg.eq.NegMul_Stack]
  simp only [rotaryMatrix]
  apply (DotAppendSHstackS.eq.AppendHstackSAddSDotS
    ((Tensor.eye (α := ℝ) d) * [_ < d] α.cos)
    ((Tensor.eye (α := ℝ) d) * [_ < d] α.sin)
    (-((Tensor.eye (α := ℝ) d) * [_ < d] α.sin))
    ((Tensor.eye (α := ℝ) d) * [_ < d] α.cos)
    ((Tensor.eye (α := ℝ) d) * [_ < d] β.cos)
    (-((Tensor.eye (α := ℝ) d) * [_ < d] β.sin))
    ((Tensor.eye (α := ℝ) d) * [_ < d] β.sin)
    ((Tensor.eye (α := ℝ) d) * [_ < d] β.cos)).trans
  simp only [id]
  rw [NegMul_Stack.eq.Mul_Stack_Neg, NegMul_Stack.eq.Mul_Stack_Neg]
  rw [DotMulSEye.eq.MulEye α.cos β.cos]
  rw [DotMulSEye.eq.MulEye α.sin β.sin]
  rw [DotMulSEye.eq.MulEye α.cos (-β.sin)]
  rw [DotMulSEye.eq.MulEye α.sin β.cos]
  rw [DotMulSEye.eq.MulEye (-α.sin) β.cos]
  rw [DotMulSEye.eq.MulEye α.cos β.sin]
  rw [DotMulSEye.eq.MulEye (-α.sin) (-β.sin)]
  repeat erw [AddMulS_Stack.eq.Mul_Stack_Add]
  have h00 : α.cos * β.cos + α.sin * β.sin = (β - α).cos := by
    rw [mul_comm α.cos, mul_comm α.sin]
    exact AddMulS.eq.CosSub β α
  have h01 : α.cos * (-β.sin) + α.sin * β.cos = -((β - α).sin) := by
    rw [Mul_Neg.eq.NegMul, add_comm, ← sub_eq_add_neg, mul_comm α.cos]
    exact (neg_sub (β.sin * α.cos) (α.sin * β.cos)).symm.trans (congrArg Neg.neg (SubMulSSin_Cos.eq.SinSub β α))
  have h10 : (-α.sin) * β.cos + α.cos * β.sin = (β - α).sin := by
    rw [MulNeg.eq.NegMul, add_comm, ← sub_eq_add_neg, mul_comm α.cos]
    exact SubMulSSin_Cos.eq.SinSub β α
  have h11 : (-α.sin) * (-β.sin) + α.cos * β.cos = (β - α).cos := by
    rw [MulNeg.eq.NegMul, Mul_Neg.eq.NegMul, neg_neg, add_comm, mul_comm α.cos, mul_comm α.sin]
    exact AddMulS.eq.CosSub β α
  rw [h00, h01, h10, h11]
  rw [Mul_Stack_Neg.eq.NegMul_Stack]


-- created on 2026-09-03
-- updated on 2026-09-05
