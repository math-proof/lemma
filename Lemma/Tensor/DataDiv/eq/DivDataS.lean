import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
  [Div α]
-- given
  (X Y : Tensor α s) :
-- imply
  (X / Y).data = X.data / Y.data := by
-- proof
  aesop


-- created on 2025-09-21
-- updated on 2025-09-24
