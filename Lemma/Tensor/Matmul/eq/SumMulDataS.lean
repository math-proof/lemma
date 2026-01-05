import Lemma.Nat.EqAddMulDiv
import sympy.tensor.tensor
open Nat


@[main]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (X Y : Tensor α [n]) :
-- imply
  X.matmul Y = ((X.data * Y.data).sum : Tensor α []) := by
-- proof
  unfold Tensor.matmul
  split_ifs
  repeat grind


-- created on 2026-01-05
