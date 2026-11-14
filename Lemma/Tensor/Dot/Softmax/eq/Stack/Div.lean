import Lemma.Tensor.BandPart.of.Ge_Sub_1
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T
import Instance.Data.Vector.Basic.Dot
open Tensor
set_option maxHeartbeats 200000


private lemma softmax_dot
  {m d : ℕ}
-- given
  (W : Tensor ℝ* [m, d])
  (X : Tensor ℝ* [m]) :
-- imply
  X.softmax ⬝ᵥ W = ((Exp.exp X) ⬝ᵥ W) / id (α := Tensor ℝ* []) ((Exp.exp X).sum 0) := by
-- proof
  have hsoft : X.softmax = X.softmax 0 := rfl
  rw [hsoft, Softmax.eq.DivExp_KeepdimSumExp, Div_KeepdimSum.eq.Div_Sum]
  apply DotDiv.eq.DivDot (Exp.exp X) ((Exp.exp X).sum 0) W

private lemma stack_softmax_dot
  {n d_z : ℕ}
-- given
  (Q K V : Tensor ℝ* [n, d_z]) :
-- imply
  ([i < n] (Q[i] ⬝ᵥ K[(i + 1 - n : ℕ):(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*)).softmax ⬝ᵥ V[(i + 1 - n : ℕ):(i + 1 : ℕ)]) =
    [i < n] ((Exp.exp (Q[i] ⬝ᵥ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))) ⬝ᵥ V[:(i + 1 : ℕ)]) / id (α := Tensor ℝ* []) (Exp.exp (Q[i] ⬝ᵥ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))).sum := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  conv_lhs => erw [EqGetStack.fin]
  conv_rhs => erw [EqGetStack.fin]
  have h0 : (i : ℕ) + 1 - n = 0 := by omega
  rw [h0]
  apply softmax_dot

@[path]
private lemma gpt
  [NeZero n]
  {d_z : ℕ}
-- given
  (Q K V : Tensor ℝ [n, d_z]) :
-- imply
  let Q : Tensor ℝ* [n, d_z] := Q
  let K : Tensor ℝ* [n, d_z] := K
  let V : Tensor ℝ* [n, d_z] := V
  let QK : Tensor ℝ* [n, n] := Q ⬝ᵥ Kᵀ
  (QK / √(d_z : ℝ*) + ((1 : Tensor ℝ* [n, n]).band_part n 0 - 1) * ∞).softmax ⬝ᵥ V ≈ [i < n]
    ((Exp.exp (Q[i] ⬝ᵥ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))) ⬝ᵥ V[:(i + 1 : ℕ)]) / id (α := Tensor ℝ* []) (Exp.exp (Q[i] ⬝ᵥ K[:(i + 1 : ℕ)]ᵀ / √(d_z : ℝ*))).sum := by
-- proof
  have h := DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T.gpt (l := n) Q K V
  intro Q K V QK
  simp only [QK, BandPart.of.Ge_Sub_1 (Nat.sub_le n 1)]
  apply h.trans (XEq.of.Eq (stack_softmax_dot Q K V))


-- created on 2023-06-18
-- updated on 2026-11-13
