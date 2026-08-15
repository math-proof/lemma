import Lemma.Tensor.DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulMul
import Lemma.Tensor.SumMul.eq.MulSum
open Tensor


@[main]
private lemma main
  [CommSemiring α]
-- given
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A * B) @ C = A @ C * B :=
-- proof
  DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS (f := (· * · : α → α → α)) MulMul.comm SumMul.eq.MulSum (zero_mul ·) hs hs' A C B


-- created on 2026-08-15
