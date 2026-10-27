import Lemma.Bool.SEqUFnS.of.SEq
import Def.Data.Holor.Defs.Part4
import Def.Data.Holor.Sum
open Bool


@[path]
private lemma main
  [Add α] [Zero α]
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i : ℕ) :
-- imply
  A.sum i ≃ B.sum i := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-06-29
-- updated on 2026-10-26
