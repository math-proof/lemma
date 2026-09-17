import Lemma.Tensor.Mul
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Tensor.Sub.eq.Add_Neg
import torch.stack
open Tensor


@[main]
private lemma main
-- given
  (c s x0 x1 : Tensor ℝ []) :
-- imply
  Add.add (c * x0) ((-s) * x1) = x0 * c - x1 * s := by
-- proof
  rw [Sub.eq.Add_Neg.nil]
  congr 1
  · apply Tensor.Mul.hComm
  · rw [MulNeg.eq.NegMul.nil, Tensor.Mul.hComm]


-- created on 2026-09-17
