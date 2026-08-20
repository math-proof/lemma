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
-- given
  (i : Fin n) :
-- imply
  (((1 : Tensor α [n, n]).band_part l u).get i).sum > 0 := by
-- proof
  have : NeZero n := ⟨Nat.ne_zero_of_lt i.isLt⟩
  apply Lt0SumGetBandPart.of.LeSub
  omega


-- created on 2026-07-28
-- updated on 2026-08-20
