import Lemma.Tensor.EqLengthS
open Tensor Nat


@[main]
private lemma main
  {X : Tensor α s}
-- given
  (i : Fin X.length)
  (Y : Tensor α s) :
-- imply
  i < Y.length := by
-- proof
  rw [EqLengthS Y X]

  apply i.isLt


-- created on 2026-07-12
