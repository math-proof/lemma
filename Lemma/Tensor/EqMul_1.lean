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
  x * (↑(1 : ℕ) : Tensor α []) = x := by
-- proof
  have h1 : (↑(1 : ℕ) : Tensor α []) = (1 : Tensor α []) := Nat.cast_one
  rw [h1, Tensor.Mul]
  apply mul_one


-- created on 2026-09-04
