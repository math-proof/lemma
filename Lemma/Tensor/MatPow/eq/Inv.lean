import sympy.matrices.expressions.matpow
import sympy.concrete.products
import Lemma.Tensor.EqMatProd
open Tensor


@[main, subst 1]
private lemma main
  [CommRing α] [CharZero α]
  {n : ℕ}
  {M : Tensor α [n, n]} :
-- imply
  M ^ (-(1 : ℤ)) = M.inv := by
-- proof
  simp only [HPow.hPow, Tensor.MatPow]
  split
  · exfalso
    simp at *
  · simp only [Int.toNat]
    exact EqMatProd M.inv


-- created on 2026-09-17
