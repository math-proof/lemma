import Lemma.Tensor.EqItem1'1
import Lemma.Tensor.ItemAbs.eq.AbsItem
import Lemma.Tensor.ItemSquare.eq.SquareItem
open Tensor


@[main]
private lemma main
  [CommRing α] [LinearOrder α] [IsStrictOrderedRing α]
  {a : Tensor α []}
-- given
  (h : a² = 1) :
-- imply
  |a| = 1 := by
-- proof
  apply Eq.of.Item
  rw [ItemAbs.eq.AbsItem, EqItem1'1]
  have hs : a.item ^ 2 = 1 := by
    have := congrArg Tensor.item h
    rwa [ItemSquare.eq.SquareItem, EqItem1'1] at this
  rw [← abs_one]
  exact (abs_eq_iff_mul_self_eq (a := a.item) (b := (1 : α))).2 (by
    simpa [pow_two] using hs)


-- created on 2026-09-07
