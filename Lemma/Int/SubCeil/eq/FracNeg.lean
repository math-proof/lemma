import Lemma.Int.Ceil.eq.NegFloorNeg
import sympy.functions.elementary.integers
import sympy.Basic
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌈x⌉ - x = fract (-x) := by
-- proof
  unfold Int.fract
  rw [Ceil.eq.NegFloorNeg, Int.cast_neg]
  abel


-- created on 2018-05-21
