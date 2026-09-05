import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub
import Lemma.Tensor.DotSoftmaxDivDot_T.eq.Stack_Div_SumExp
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.RotaryMatrix.eq.AppendHstackSMulSEye
import Lemma.Tensor.RotaryMatrixSubGetS.eq.Ite_RotaryMatrix_T.of.Eq_Stack_Mul
open Fin Tensor
set_option maxHeartbeats 4000000


/--
the standard frequency hypothesis is
(hθ : θ = [i < n] [j < d] ↑(«λ» * i / b ^ (j / (d : ℝ)))), here we generalize it a simple linear function.
-/
@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
-- given
  (hθ : θ = [i < n] (τ * (i : ℝ)))
  (Q K V : Tensor ℝ [n, d + d]) :
-- imply
  let R (i : Fin n) := θ[i].rotaryMatrix
  let Rel (i k : Fin n) : Tensor ℝ [d + d, d + d] :=
    if k ≥ i then
      R (k - i)
    else
      (R (i - k))ᵀ
  (([i < n] (R i) @ Q[i]) @ ([i < n] (R i) @ K[i])ᵀ / √↑(d + d)).softmax @ V = [i < n] [j < d + d] (∑ k : Fin n, V[k][j] * exp (id (α := Tensor ℝ []) (Q[i] @ ((Rel i k) @ K[k]) / √↑(d + d)))) / id (α := Tensor ℝ []) (exp (((R i) @ Q[i]) @ ([i < n] (R i) @ K[i])ᵀ / √↑(d + d))).sum := by
-- proof
  intro R Rel
  apply (DotSoftmaxDivDot_T.eq.Stack_Div_SumExp _ _ _).trans
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
  apply congrArg₂
  ·
    apply Sum.of.All_Eq
    intro k
    apply congrArg₂
    ·
      rfl
    ·
      apply congrArg exp
      apply congrArg (id (α := Tensor ℝ []))
      apply congrArg (fun t : Tensor ℝ [] => t / √↑(d + d))
      apply Eq.trans (b := ((R i) @ Q[i]) @ ((R k) @ K[k]))
      ·
        apply congrArg₂ <;> apply EqGetStack.fin
      ·
        apply Eq.trans (DotDotSRotaryMatrix.eq.Dot_DotRotaryMatrixSub θ[i] θ[k] Q[i] K[k])
        apply congrArg (fun t : Tensor ℝ [d + d, d + d] => Q[i] @ (t @ K[k]))
        exact RotaryMatrixSubGetS.eq.Ite_RotaryMatrix_T.of.Eq_Stack_Mul (i := i) (j := k) hθ
  ·
    apply congrArg (fun t : Tensor ℝ [d + d] => id (α := Tensor ℝ []) (exp (t @ ([i < n] (R i) @ K[i])ᵀ / √↑(d + d))).sum)
    apply EqGetStack.fin


-- created on 2023-06-09
-- updated on 2026-09-05
