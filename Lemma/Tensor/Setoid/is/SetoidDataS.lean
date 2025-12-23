import sympy.Basic
import sympy.tensor.functions


@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Tensor ℝ* s) :
-- imply
  A ≈ B ↔ A.data ≈ B.data := by
-- proof
  cases A
  cases B
  aesop


-- created on 2025-12-23
