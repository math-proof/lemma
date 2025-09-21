import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
  [Div α]
-- given
  (X Y : Tensor α s):
-- imply
  (X / Y).data = X.data / Y.data := by
-- proof
  aesop


@[main]
private lemma scalar
  [Div α]
-- given
  (X : Tensor α s)
  (n : Tensor α []):
-- imply
  (X / n).data = X.data / n.data[0] := by
-- proof
  aesop


-- created on 2025-09-21
