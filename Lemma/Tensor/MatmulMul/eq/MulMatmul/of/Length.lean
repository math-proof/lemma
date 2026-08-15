import Lemma.Tensor.MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulMul
import Lemma.Tensor.SumMul.eq.MulSum
open Tensor


@[main]
private lemma main
  [CommSemiring α]
  {s s' : List ℕ}
-- given
  (hlen : s.length = s'.length)
  (A : Tensor α (s ++ [m, t]))
  (C : Tensor α (s' ++ [t, k]))
  (B : Tensor α []) :
-- imply
  (A * B).matmul C hlen = A.matmul C hlen * B :=
-- proof
  MatmulBFn.eq.BFnMatmul.of.Length.All_EqBFn0.All_EqSumMap.All_EqMapS (f := (· * · : α → α → α)) MulMul.comm SumMul.eq.MulSum (zero_mul ·) hlen A C B


-- created on 2026-08-15
