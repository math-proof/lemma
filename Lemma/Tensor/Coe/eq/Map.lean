import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Coe α β]
-- given
  (X : Tensor α s) :
-- imply
  (X : Tensor β s) = X.map Coe.coe := by
-- proof
  cases X
  simp [Tensor.map]


-- created on 2026-07-28
