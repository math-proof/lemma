import Lemma.Bool.SEqUFnS.of.SEq
import Def.Data.Holor.Defs.Part4
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
