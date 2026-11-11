import Def.Data.Tensor.Stack.Part2
import Def.Data.Tensor.Prod


@[path]
private lemma main
-- given
  (X : Tensor α s):
-- imply
  X.data.length = s.prod := by
-- proof
  rfl


-- created on 2025-06-29
