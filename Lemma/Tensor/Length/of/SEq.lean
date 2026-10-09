import stdlib.SEq
import Lemma.Tensor.Length.of.Eq
open Tensor


@[path]
private lemma main
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  X.length = Y.length := by
-- proof
  apply Length.of.Eq h.left


@[path]
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
