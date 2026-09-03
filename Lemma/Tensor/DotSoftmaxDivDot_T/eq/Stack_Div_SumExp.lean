import Lemma.Fin.Sum.of.All_Eq
import Lemma.List.EqSwap_0'1
import Lemma.Tensor.Div_KeepdimSum.eq.Div_Sum
import Lemma.Tensor.Dot.eq.Sum_MulGetS
import Lemma.Tensor.DotDiv.eq.DivDot
import Lemma.Tensor.DotSoftmaxDivDot_T.eq.Stack_Dot_GetT
import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetDot.eq.Dot_GetT
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.GetTCast_T.eq.Get
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Mul
import Lemma.Tensor.SEqDotS.of.SEq
import Lemma.Tensor.SEqExpS.of.SEq
import Lemma.Tensor.SEqSoftmaxS.of.SEq
import Lemma.Tensor.SEqSumS.of.SEq
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
open Fin List Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma main
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  (Q @ Kᵀ / √d_z).softmax @ V = [i < n] [j < d_z] (∑ k : Fin n, V[k][j] * exp (id (α := Tensor ℝ []) (Q[i] @ K[k] / √d_z))) / id (α := Tensor ℝ []) (exp (Q[i] @ Kᵀ / √d_z)).sum := by
-- proof
  rw [DotSoftmaxDivDot_T.eq.Stack_Dot_GetT]
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs =>
    erw [EqGetStack.fin (i := i)]
    erw [EqGetStack.fin (i := j)]
  conv_rhs =>
    erw [EqGetStack.fin (i := i)]
    erw [EqGetStack.fin (i := j)]
  let KT : Tensor ℝ [d_z, n] := cast (congrArg (Tensor ℝ) (EqSwap_0'1 n d_z)) Kᵀ
  have hX : ((Q[i] : Tensor ℝ [d_z]) @ Kᵀ) / √d_z ≃ ((Q[i] : Tensor ℝ [d_z]) @ KT) / √d_z := by
    apply Bool.SEqUFnS.of.SEq _ (fun {s} (X : Tensor ℝ s) => X / √d_z)
    apply SEqDotS.of.SEq.left
    apply Bool.SEqCast.of.Eq (EqSwap_0'1 n d_z)
  apply Eq.trans (b := (((Q[i] : Tensor ℝ [d_z]) @ KT) / √d_z).softmax @ (Vᵀ[j] : Tensor ℝ [n]))
  ·
    apply Bool.Eq.of.SEq
    apply SEqDotS.of.SEq
    apply SEqSoftmaxS.of.SEq hX
  ·
    let X : Tensor ℝ [n] := ((Q[i] : Tensor ℝ [d_z]) @ KT) / √d_z
    let v : Tensor ℝ [n] := Vᵀ[j]
    have hsoft : X.softmax = X.softmax 0 := rfl
    apply Eq.trans (congrArg (fun t => t @ v) (hsoft.trans (Softmax.eq.DivExp_KeepdimSumExp X 0)))
    apply Eq.trans (congrArg (fun t => t @ v) (Div_KeepdimSum.eq.Div_Sum (exp X)))
    apply Eq.trans (DotDiv.eq.DivDot (exp X) (id (α := Tensor ℝ []) ((exp X).sum 0)) v)
    apply congrArg₂
    ·
      apply (Dot.eq.Sum_MulGetS _ _).trans
      apply Sum.of.All_Eq
      intro k
      apply Eq.trans (Tensor.Mul _ _)
      apply Eq.trans (Tensor.Mul.comm _ _)
      apply Eq.trans (Tensor.Mul _ _).symm
      apply congrArg id
      apply congrArg₂
      ·
        apply GetTranspose.eq.Get
      ·
        apply Eq.trans (GetExp.eq.ExpGet _ _)
        apply congrArg exp
        apply Eq.trans (GetDiv.eq.DivGet.scalar _ _ _)
        convert congrArg (fun t : Tensor ℝ [] => t / √d_z) ((GetDot.eq.Dot_GetT _ KT _).trans (congrArg (Q[i] @ ·) (GetTCast_T.eq.Get _ _)))
        rfl
    ·
      apply Bool.Eq.of.SEq
      apply SEqSumS.of.SEq
      apply SEqExpS.of.SEq hX.symm


-- created on 2023-05-22
