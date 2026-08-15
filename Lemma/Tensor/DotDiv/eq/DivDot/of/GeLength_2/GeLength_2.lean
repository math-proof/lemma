import Lemma.Tensor.DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.SumDiv.eq.DivSum
open Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (hs : s.length ≥ 2)
  (hs' : s'.length ≥ 2)
  (A : Tensor α s)
  (C : Tensor α s')
  (B : Tensor α []) :
-- imply
  (A / B) @ C = A @ C / B :=
-- proof
  DotBFn.eq.BFnDot.of.GeLength_2.GeLength_2.All_EqBFn0.All_EqSumMap.All_EqMapS
    MulDiv.eq.DivMul SumDiv.eq.DivSum (fun b => zero_div b) hs hs' A C B


-- created on 2026-08-13
-- updated on 2026-08-15
