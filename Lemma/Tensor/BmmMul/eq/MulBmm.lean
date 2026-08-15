import Lemma.Tensor.BmmBFn.eq.BFnBmm
import Lemma.Tensor.MulMul
import Lemma.Tensor.SumMul.eq.MulSum
open Tensor


@[main]
private lemma main
  [CommSemiring α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A * B).bmm C = A.bmm C * B :=
-- proof
  BmmBFn.eq.BFnBmm (f := (· * · : α → α → α))
    MulMul.comm
    SumMul.eq.MulSum
    A C B


-- created on 2026-08-15
