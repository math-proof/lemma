import Lemma.Tensor.DotMap.eq.MapDot.of.All_Eq_Map.All_EqMulMap.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulDiv.eq.DivMul
import Lemma.Tensor.SumDiv.eq.DivSum
open Tensor


@[main]
private lemma main
  [Semifield α]
-- given
  (A : Tensor α s)
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A / B) @ C = A @ C / B :=
-- proof
  DotMap.eq.MapDot.of.All_Eq_Map.All_EqMulMap.All_EqBFn0.All_EqSumMap.All_EqMapS
    MulDiv.eq.DivMul SumDiv.eq.DivSum (zero_div ·) MulDiv.eq.DivMul.right MulDiv.eq.DivMul.left A B C


-- created on 2026-08-11
-- updated on 2026-08-16
