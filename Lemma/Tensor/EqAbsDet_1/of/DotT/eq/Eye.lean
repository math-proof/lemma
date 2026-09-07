import Lemma.Tensor.EqSquareDet_1.of.DotT.eq.Eye
import Lemma.Tensor.EqAbs_1.of.EqSquare_1
open Tensor


@[main]
private lemma main
  [CommRing α] [CharZero α] [LinearOrder α] [IsStrictOrderedRing α]
  {X : Tensor α [n, n]}
-- given
  (h : Xᵀ @ X = Tensor.eye (α := α) n) :
-- imply
  |X.det| = 1 := by
-- proof
  exact EqAbs_1.of.EqSquare_1 (a := (X.det : Tensor α [])) (EqSquareDet_1.of.DotT.eq.Eye h)


-- created on 2026-09-07
