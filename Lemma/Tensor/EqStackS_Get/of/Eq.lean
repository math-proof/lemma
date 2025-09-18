import sympy.tensor.Basic
import sympy.tensor.stack
import Lemma.Basic


@[main]
private lemma main
  {x y : Tensor (Fin n) [n]}
  {a : Tensor α [n]}
-- given
  (h : x = y) :
-- imply
  [i < n] a[x[i]] = [i < n] a[y[i]] := by
-- proof
  rw [h]


-- created on 2025-05-01
