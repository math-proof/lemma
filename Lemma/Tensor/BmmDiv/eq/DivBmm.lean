import Lemma.Tensor.BmmBFn.eq.BFnBmm
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.SumDiv.eq.DivSum
open Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (A : Tensor α (bz ++ [m, k]))
  (C : Tensor α (bz ++ [k, n]))
  (B : Tensor α []) :
-- imply
  (A / B).bmm C = A.bmm C / B :=
-- proof
  BmmBFn.eq.BFnBmm
    MulDiv.eq.DivMul
    SumDiv.eq.DivSum
    A C B


-- created on 2026-08-13
-- updated on 2026-08-15
