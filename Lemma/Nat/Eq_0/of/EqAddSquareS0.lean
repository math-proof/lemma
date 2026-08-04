import Lemma.Bool.Ne.is.NotEq
import Lemma.Int.GeSquare_0
import Lemma.Nat.GtSquare_0.of.Ne_0
import Lemma.Nat.Lt0Add.of.Ge_0.Gt_0
open Nat Int Bool


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  [NoZeroDivisors α] [NeZero (1 : α)]
  {x y : α}
-- given
  (h : x² + y² = 0) :
-- imply
  x = 0 := by
-- proof
  by_contra hx
  have hx' := Ne.is.NotEq.mp hx
  have h_pos := Lt0Add.of.Ge_0.Gt_0 (GeSquare_0 y) (GtSquare_0.of.Ne_0 hx')
  have h_gt : x² + y² > 0 := by
    convert h_pos using 1
    ac_rfl
  rw [h] at h_gt
  exact lt_irrefl 0 h_gt


-- created on 2026-08-04
