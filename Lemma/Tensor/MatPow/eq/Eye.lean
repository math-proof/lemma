import sympy.matrices.expressions.matpow
import sympy.concrete.products


@[main, subst 0]
private lemma main
  [CommRing α] [CharZero α]
  {n : ℕ}
  {M : Tensor α [n, n]} :
-- imply
  M ^ (0 : ℤ) = Tensor.eye n := by
-- proof
  simp [HPow.hPow, Tensor.MatPow, Tensor.matProd]


-- created on 2026-09-17
