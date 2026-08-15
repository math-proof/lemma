import Lemma.Tensor.MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.SumDiv.eq.DivSum
open Tensor


@[main]
private lemma main
  [Semifield α]
  {s s' : List ℕ}
-- given
  (hlen : s.length = s'.length)
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s' ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A / B).matmul C hlen = A.matmul C hlen / B :=
-- proof
  MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS MulDiv.eq.DivMul SumDiv.eq.DivSum (zero_div ·) hlen A C B


-- created on 2026-08-15
