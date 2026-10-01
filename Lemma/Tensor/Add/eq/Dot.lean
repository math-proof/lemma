import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


@[main]
private lemma main
  [NonUnitalNonAssocSemiring α]
  {n : ℕ}
  {x a b : Matrix (Fin n) (Fin n) α} :
-- imply
  x * a + x * b = x * (a + b) :=
-- proof
  (Matrix.mul_add x a b).symm


-- created on 2021-12-26
