import sympy.Basic
import sympy.tensor.Basic


@[main]
private lemma main
  [Add α]
-- given
  (X : Tensor α s)
  (a : α) :
-- imply
  (X + a).data = X.data + a :=
-- proof
  rfl


-- created on 2025-12-01
