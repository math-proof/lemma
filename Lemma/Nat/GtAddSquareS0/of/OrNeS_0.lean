import Lemma.Int.GeSquare_0
import Lemma.Nat.GtSquare_0.of.Ne_0
import Lemma.Nat.Lt0Add.of.Ge_0.Gt_0
open Nat Int


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  [NoZeroDivisors α] [NeZero (1 : α)]
  {x y : α}
-- given
  (h : x ≠ 0 ∨ y ≠ 0) :
-- imply
  x² + y² > 0 := by
-- proof
  obtain hx | hy := h
  ·
    convert Lt0Add.of.Ge_0.Gt_0 (GeSquare_0 y) (GtSquare_0.of.Ne_0 hx) using 1
    ac_rfl
  ·
    exact Lt0Add.of.Ge_0.Gt_0 (GeSquare_0 x) (GtSquare_0.of.Ne_0 hy)


-- created on 2018-07-15
