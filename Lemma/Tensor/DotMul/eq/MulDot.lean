import Lemma.Tensor.DotMap.eq.MapDot.of.All_Eq_Map.All_EqMulMap.All_EqBFn0.All_EqSumMap.All_EqMapS
import Lemma.Tensor.MulMul
import Lemma.Tensor.SumMul.eq.MulSum
open Tensor


@[main]
private lemma main
  [CommSemiring α]
-- given
  (A : Tensor α s)
  (B : Tensor α [])
  (C : Tensor α s') :
-- imply
  (A * B) @ C = A @ C * B :=
-- proof
  DotMap.eq.MapDot.of.All_Eq_Map.All_EqMulMap.All_EqBFn0.All_EqSumMap.All_EqMapS (f := (· * · : α → α → α))
    MulMul.comm SumMul.eq.MulSum (zero_mul ·) MulMul.comm.right MulMul.comm.left A B C


-- created on 2026-08-15
-- updated on 2026-08-16
