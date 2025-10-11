import sympy.tensor.functions
import sympy.Basic


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s) :
-- imply
  (exp X).data = exp X.data :=
-- proof
  rfl


-- created on 2025-10-11
