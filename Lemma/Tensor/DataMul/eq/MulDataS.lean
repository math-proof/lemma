import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α s) :
-- imply
  (A * B).data = A.data * B.data :=
-- proof
  rfl


-- created on 2025-05-02
-- updated on 2025-12-01
