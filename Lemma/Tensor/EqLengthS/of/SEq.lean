import stdlib.SEq
import sympy.tensor.tensor
import Lemma.Tensor.EqLengthS.of.Eq
open Tensor


@[main]
private lemma main
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  X.length = Y.length := by
-- proof
  apply EqLengthS.of.Eq h.left


@[main]
private lemma shape
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  s.length = s'.length := by
-- proof
  rw [h.left]


-- created on 2025-06-24
-- updated on 2025-10-08
