import Lemma.Tensor.GtSumData_0.is.GtSum_0
import Lemma.Tensor.Le.is.LeDataS
import Lemma.Vector.Lt0SumMul.of.GtSum_0.Ge_0.Gt_0
open Tensor


@[main]
private lemma main
  [Semiring α] [PartialOrder α] [IsOrderedCancelAddMonoid α] [PosMulStrictMono α]
  {X Y : Tensor α [n]}
-- given
  (h_X : X > 0)
  (h_Y : Y ≥ 0)
  (h_sum : Y.sum > 0) :
-- imply
  (X * Y).sum > 0 := by
-- proof
  apply GtSum_0.of.GtSumData_0
  apply Vector.Lt0SumMul.of.GtSum_0.Ge_0.Gt_0 _ _ (GtSumData_0.of.GtSum_0 h_sum)
  · simpa [gt_iff_lt, Lt.is.LtDataS, EqData0'0] using h_X
  · simpa [ge_iff_le, Le.is.LeDataS, EqData0'0] using h_Y


-- created on 2026-07-29
