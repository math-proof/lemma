import Lemma.Tensor.DotBFn.eq.BFnDot.of.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.SumDiv.eq.DivSum
open Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (hs' : s'.length ≥ 2)
  (A : Tensor α [n])
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B :=
-- proof
  DotBFn.eq.BFnDot.of.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS MulDiv.eq.DivMul SumDiv.eq.DivSum (zero_div ·) hs' A C B


@[main]
private lemma left
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α [n'])
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B :=
-- proof
  DotBFn.eq.BFnDot.of.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS.left MulDiv.eq.DivMul SumDiv.eq.DivSum (zero_div ·) hs A C B


-- created on 2026-08-13
-- updated on 2026-08-15
