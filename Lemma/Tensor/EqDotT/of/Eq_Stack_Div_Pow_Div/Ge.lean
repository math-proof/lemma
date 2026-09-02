import Lemma.Tensor.AddMulS_Stack.eq.Mul_Stack_Add
import Lemma.Tensor.CosSub.eq.AddMulS
import Lemma.Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS
import Lemma.Tensor.DotMulSEye.eq.MulEye
import Lemma.Tensor.Mul_Neg.eq.NegMul
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Tensor.NegMul_Stack.eq.Mul_Stack_Neg
import Lemma.Tensor.SinSub.eq.SubMulSSin_Cos
import Lemma.Tensor.SubGetS.eq.Get_Sub.of.Ge
import Lemma.Tensor.TAppendHstackS.eq.AppendHstackSTS
import Lemma.Tensor.TMulEye.eq.MulEye
open Tensor
set_option maxHeartbeats 800000


noncomputable def rotaryMatrix (θ : Tensor ℝ [d]) : Tensor ℝ [d + d, d + d] :=
  let I : Tensor ℝ [d, d] := Tensor.eye d
  (I * [_ < d] θ.cos).hstack (-(I * [_ < d] θ.sin)) ++ (I * [_ < d] θ.sin).hstack (I * [_ < d] θ.cos)


@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d / 2]}
  {b : ℕ}
  {lam : ℝ}
  {k t : Fin n}
-- given
  (h : t ≤ k)
  (hθ : θ = [i < n] [j < d / 2] ↑(lam * i / b ^ (j / (d / 2 : ℝ)))) :
-- imply
  let R (i : Fin n) :=
    let I := Tensor.eye (d / 2)
    let θᵢ : Tensor ℝ [d / 2] := θ[i]
    (I * [_ < d / 2] θᵢ.cos).hstack (-(I * [_ < d / 2] θᵢ.sin)) ++ (I * [_ < d / 2] θᵢ.sin).hstack (I * [_ < d / 2] θᵢ.cos)
  (R t)ᵀ @ R k = R (k - t) := by
-- proof
  intro R
  extract_lets I at R
  have hR (i : Fin n) : R i = rotaryMatrix (θ[i] : Tensor ℝ [d / 2]) := by simp [R, rotaryMatrix, I]
  rw [hR t, hR k, hR (k - t)]
  refine Eq.trans ?_ (congrArg rotaryMatrix (SubGetS.eq.Get_Sub.of.Ge hθ h))
  let α : Tensor ℝ [d / 2] := θ[t]
  let β : Tensor ℝ [d / 2] := θ[k]
  change (rotaryMatrix α)ᵀ @ (rotaryMatrix β) = rotaryMatrix (β - α)
  conv_lhs =>
    arg 1
    simp only [rotaryMatrix]
    rw [NegMul_Stack.eq.Mul_Stack_Neg]
    rw [TAppendHstackS.eq.AppendHstackSTS]
    rw [TMulEye.eq.MulEye α.cos, TMulEye.eq.MulEye α.sin, TMulEye.eq.MulEye (-α.sin)]
    rw [← NegMul_Stack.eq.Mul_Stack_Neg]
  simp only [rotaryMatrix]
  apply (DotAppendSHstackS.eq.AppendHstackSAddSDotS
    ((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] α.cos)
    ((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] α.sin)
    (-((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] α.sin))
    ((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] α.cos)
    ((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] β.cos)
    (-((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] β.sin))
    ((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] β.sin)
    ((Tensor.eye (α := ℝ) (d / 2)) * [_ < d / 2] β.cos)).trans
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
    exact (CosSub.eq.AddMulS β α).symm
  have h01 : α.cos * (-β.sin) + α.sin * β.cos = -((β - α).sin) := by
    rw [Mul_Neg.eq.NegMul, add_comm, ← sub_eq_add_neg, mul_comm α.cos]
    exact ((congrArg Neg.neg (SinSub.eq.SubMulSSin_Cos β α)).trans (neg_sub (β.sin * α.cos) (α.sin * β.cos))).symm
  have h10 : (-α.sin) * β.cos + α.cos * β.sin = (β - α).sin := by
    rw [MulNeg.eq.NegMul, add_comm, ← sub_eq_add_neg, mul_comm α.cos]
    exact (SinSub.eq.SubMulSSin_Cos β α).symm
  have h11 : (-α.sin) * (-β.sin) + α.cos * β.cos = (β - α).cos := by
    rw [MulNeg.eq.NegMul, Mul_Neg.eq.NegMul, neg_neg, add_comm, mul_comm α.cos, mul_comm α.sin]
    exact (CosSub.eq.AddMulS β α).symm
  rw [h00, h01, h10, h11]
  rw [← NegMul_Stack.eq.Mul_Stack_Neg]


-- created on 2023-09-16
-- updated on 2026-09-02
