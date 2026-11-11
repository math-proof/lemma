import Lemma.Bool.SEqUFnS.of.SEq
import Def.Data.Tensor.Defs.Part4
import Notation.Data.Tensor.Permute
open Bool


@[path]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h : A ≃ B)
  (i j : ℕ) :
-- imply
  A.transpose i j ≃ B.transpose i j := by
-- proof
  apply SEqUFnS.of.SEq h


-- created on 2025-07-13
