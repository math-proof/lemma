import sympy.tensor.stack
import Lemma.Basic


@[main]
private lemma main
-- given
  (X : Tensor α s):
-- imply
  X.data.length = s.prod := by
-- proof
  rfl


-- created on 2025-06-29
