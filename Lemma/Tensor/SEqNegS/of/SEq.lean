import Lemma.Bool.SEqUFnS.of.SEq
import Instance.Data.Tensor.Defs.Part2
open Bool


@[path]
private lemma main
  [Neg α]
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  -X ≃ -Y := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-12-04
-- updated on 2026-11-20
