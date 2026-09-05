import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Mul
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetMul.eq.MulGet
import sympy.tensor.tensor
open Tensor Vector


@[main]
private lemma nat
  [Semiring α]
  [CharZero α]
-- given
  (x : Tensor α []) :
-- imply
  x * (↑(0 : ℕ) : Tensor α []) = 0 := by
-- proof
  erw [Nat.cast_zero, Tensor.Mul]
  apply MulZeroClass.mul_zero


@[main]
private lemma main
  [MulZeroClass α]
-- given
  (X : Tensor α s) :
-- imply
  X * (0 : Tensor α []) = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData.head]
  rw [EqData0'0]
  ext i
  rw [GetMul.eq.MulGet.fin]
  erw [EqGet0_0.fin]
  apply MulZeroClass.mul_zero


-- created on 2026-09-04
-- updated on 2026-09-05
