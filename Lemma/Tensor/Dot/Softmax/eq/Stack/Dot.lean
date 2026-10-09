import sympy.Basic
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.XEq.is.All_XEqGetS
import Mathlib.Analysis.SpecialFunctions.Exp
open Tensor
set_option maxHeartbeats 1000000


@[path]
private lemma scaled_dot_product_attention
  {n d : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {V : Matrix (Fin n) (Fin d) ℝ} :
-- imply
  (Matrix.of fun i j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) * V =
    Matrix.of fun i => Matrix.vecMul (fun j => Real.exp (A i j) / ∑ k, Real.exp (A i k)) V := by
-- proof
  ext i l
  rfl


/--
batched causal attention: for every batch index \(b\), the hyperreal masked softmax
\(\operatorname{softmax}(A_b + (\Xi - 1) \cdot \infty) V_b\) with the lower-triangular band \(\Xi\)
is infinitely close to the softmax over the causal window \([0, i]\) of each row.
-/
@[path]
private lemma gpt.batched
  [NeZero n]
  {m d : ℕ}
-- given
  (A : Tensor ℝ [m, n, n])
  (V : Tensor ℝ [m, n, d]) :
-- imply
  let Ξ := (1 : Tensor ℝ* [n, n]).band_part (n - 1) 0
  let Aᵦ : Fin m → Tensor ℝ [n, n] := fun b => A[b]
  let Vᵦ : Fin m → Tensor ℝ [n, d] := fun b => V[b]
  [b < m] (((Aᵦ b : Tensor ℝ [n, n]) : Tensor ℝ* [n, n]) + (Ξ - 1) * ∞).softmax @ ((Vᵦ b : Tensor ℝ [n, d]) : Tensor ℝ* [n, d]) ≈
    [b < m] [i < n] (((Aᵦ b : Tensor ℝ [n, n]) : Tensor ℝ* [n, n])[i, (i + 1 - n : ℕ):(i + 1 : ℕ)].softmax @ ((Vᵦ b : Tensor ℝ [n, d]) : Tensor ℝ* [n, d])[(i + 1 - n : ℕ):(i + 1 : ℕ)]) := by
-- proof
  intro Ξ Aᵦ Vᵦ
  apply XEq.of.All_XEqGetS.fin
  intro b
  erw [EqGetStack.fin, EqGetStack.fin]
  exact Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax (l := n) (u := 1) (Aᵦ b) (Vᵦ b)


-- created on 2021-08-07
-- updated on 2026-09-27
