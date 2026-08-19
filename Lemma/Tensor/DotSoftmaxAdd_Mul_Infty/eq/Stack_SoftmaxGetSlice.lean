import Lemma.Nat.Sub.eq.Zero.of.Le
import Lemma.Tensor.BandPart.of.Ge_Sub_1
import Lemma.Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.XEq.of.Eq
open Nat Tensor


@[main]
private lemma main
  [NeZero (n : ℕ)]
  [NeZero (d_z : ℕ)]
-- given
  (A : Tensor ℝ [n, n])
  (V : Tensor ℝ [n, d_z]) :
-- imply
  let A : Tensor ℝ* [n, n] := A
  let V : Tensor ℝ* [n, d_z] := V
  (A + ((1 : Tensor ℝ* [n, n]).band_part n 0 - 1) * ∞).softmax @ V ≈ [i < n] A[i][:i + 1].softmax @ V[:i + 1] := by
-- proof
  simp only [BandPart.of.Ge_Sub_1 (Nat.sub_le n 1)]
  have h := DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmax (l := n) (u := 1) (n := n) (d_z := d_z) A V
  refine h.trans (XEq.of.Eq ?_)
  apply Eq.of.All_EqGetS.fin
  intro i
  grind [EqGetStack.fin]


-- created on 2026-08-17
