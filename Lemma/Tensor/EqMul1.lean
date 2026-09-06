import Lemma.Tensor.DataMul.eq.Mul_Data
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Mul
import Lemma.Vector.GetMul.eq.Mul_Get
import sympy.tensor.tensor
open Tensor Vector


@[main]
private lemma main
  [MulOneClass α]
-- given
  (X : Tensor α []) :
-- imply
  (1 : Tensor α []) * X = X := by
-- proof
  rw [Tensor.Mul]
  apply one_mul


@[main]
private lemma nat
  [Semiring α]
  [CharZero α]
-- given
  (x : Tensor α []) :
-- imply
  (↑(1 : ℕ) : Tensor α []) * x = x := by
-- proof
  erw [Nat.cast_one]
  apply main


-- created on 2026-09-04
-- updated on 2026-09-05
