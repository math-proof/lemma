import Lemma.Tensor.BandPart.of.Ge_Sub_1
import Lemma.Tensor.DotDiv.eq.DivDot
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T
import Lemma.Tensor.Div_KeepdimSum.eq.Div_Sum
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Softmax.eq.DivExp_KeepdimSumExp
import Lemma.Tensor.XEq.of.Eq
open Tensor
set_option maxHeartbeats 400000


private lemma softmax_dot
  {m d : ℕ}
  (W : Tensor ℝ* [m, d])
  (X : Tensor ℝ* [m]) :
  X.softmax @ W = ((exp X) @ W) / id (α := Tensor ℝ* []) ((exp X).sum 0) := by
  have hsoft : X.softmax = X.softmax 0 := rfl
  rw [hsoft, Softmax.eq.DivExp_KeepdimSumExp, Div_KeepdimSum.eq.Div_Sum]
  exact DotDiv.eq.DivDot (exp X) ((exp X).sum 0) W


private lemma stack_softmax_dot
  {n d_z : ℕ}
  (Q K V : Tensor ℝ* [n, d_z]) :
  ([i < n] (Q[i] @ K[(i + 1 - n : ℕ):(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*)).softmax @ V[(i + 1 - n : ℕ):(i + 1 : ℕ)]) =
    [i < n] ((exp (Q[i] @ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))) @ V[:(i + 1 : ℕ)]) / id (α := Tensor ℝ* []) (exp (Q[i] @ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))).sum := by
  apply Eq.of.All_EqGetS.fin
  intro i
  conv_lhs => erw [EqGetStack.fin]
  conv_rhs => erw [EqGetStack.fin]
  have h0 : (i : ℕ) + 1 - n = 0 := by omega
  rw [h0]
  exact softmax_dot _ _


@[main]
private lemma gpt
  [NeZero n]
  {d_z : ℕ}
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  let Q : Tensor ℝ* [n, d_z] := Q
  let K : Tensor ℝ* [n, d_z] := K
  let V : Tensor ℝ* [n, d_z] := V
  let QK : Tensor ℝ* [n, n] := Q @ Kᵀ
  (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part n 0 - 1) * ∞).softmax @ V ≈ [i < n]
    ((exp (Q[i] @ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))) @ V[:(i + 1 : ℕ)]) / id (α := Tensor ℝ* []) (exp (Q[i] @ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))).sum := by
-- proof
  have h := Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T.gpt (l := n) Q K V
  intro Q K V QK
  simp only [QK, BandPart.of.Ge_Sub_1 (Nat.sub_le n 1)]
  exact h.trans (Tensor.XEq.of.Eq (stack_softmax_dot Q K V))


-- created on 2023-06-18
