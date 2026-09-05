import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Vector.GetMul.eq.MulGet
import Lemma.Tensor.Mul
import sympy.tensor.tensor
open Tensor Vector


@[main]
private lemma nat
  [Semiring α]
  [CharZero α]
-- given
  (x : Tensor α []) :
-- imply
  x * (↑(1 : ℕ) : Tensor α []) = x := by
-- proof
  erw [Nat.cast_one, Tensor.Mul]
  apply mul_one


@[main]
private lemma main
  [MulOneClass α]
-- given
  (X : Tensor α s) :
-- imply
  X * (1 : Tensor α []) = X := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData.head]
  ext i
  rw [GetMul.eq.MulGet.fin]
  apply mul_one


-- created on 2026-09-04
