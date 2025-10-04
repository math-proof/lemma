import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Neg α]
-- given
  (X : Tensor α s) :
-- imply
  (-X).data = -X.data :=
-- proof
  rfl


-- created on 2025-10-04
