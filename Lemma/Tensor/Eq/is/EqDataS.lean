import sympy.tensor.Basic
import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Tensor α s) :
-- imply
  A = B ↔ A.data = B.data := by
-- proof
  cases A
  cases B
  simp


-- created on 2025-05-06
