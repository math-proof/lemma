import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Mul α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  (X * a).data = X.data * a :=
-- proof
  rfl


@[main]
private lemma head
  [Mul α]
-- given
  (A : Tensor α s)
  (B : Tensor α []) :
-- imply
  (A * B).data = A.data * B.data[0] :=
-- proof
  rfl


-- created on 2025-12-01
