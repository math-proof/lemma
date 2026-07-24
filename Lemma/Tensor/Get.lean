import sympy.tensor.tensor
import sympy.Basic


@[main]
private lemma main
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  X.get i = X[i] := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-12
