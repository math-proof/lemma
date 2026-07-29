import Lemma.Tensor.Lt0SumGetBandPart.of.LeSub
import sympy.matrices.expressions.special
open Tensor


@[main]
private lemma main
  [AddCommMonoidWithOne α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [IsOrderedCancelAddMonoid α]
  [NeZero (1 : α)]
  [NeZero n]
-- given
  (i : Fin n) :
-- imply
  (((1 : Tensor α [n, n]).band_part l u).get i).sum > 0 := by
-- proof
  apply Lt0SumGetBandPart.of.LeSub
  omega


-- created on 2026-07-28
