import Lemma.Bool.SEqUFnS.of.SEq
import Theorem.Data.Holor.Functions
open Bool


@[path]
private lemma main
  [Exp α]
  {X : Tensor α s}
  {Y : Tensor α s'}
-- given
  (h : X ≃ Y) :
-- imply
  exp X ≃ exp Y := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-12-04
