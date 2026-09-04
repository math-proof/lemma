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
  (↑(1 : ℕ) : Tensor α []) * x = x := by
-- proof
  have h1 : (↑(1 : ℕ) : Tensor α []) = (1 : Tensor α []) := Nat.cast_one
  rw [h1, Tensor.Mul]
  apply one_mul


-- created on 2026-09-04
