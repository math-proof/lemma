import Lemma.Tensor.Mul
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Semiring α]
  [CharZero α]
-- given
  (x : Tensor α []) :
-- imply
  x * (↑(0 : ℕ) : Tensor α []) = 0 := by
-- proof
  have h0 : (↑(0 : ℕ) : Tensor α []) = (0 : Tensor α []) := Nat.cast_zero
  rw [h0, Tensor.Mul]
  apply MulZeroClass.mul_zero


-- created on 2026-09-04
