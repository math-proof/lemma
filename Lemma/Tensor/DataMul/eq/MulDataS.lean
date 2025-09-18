import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
  [Mul α]
  {a b : Tensor α s} :
-- imply
  (a * b).data = a.data * b.data :=
-- proof
  rfl


-- created on 2025-05-02
-- updated on 2025-06-22
