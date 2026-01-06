import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Mul α]
-- given
  (a : α)
  (X : Tensor α s) :
-- imply
  (a * X).data = a * X.data :=
-- proof
  rfl


-- created on 2026-01-06
