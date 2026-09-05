import Lemma.Tensor.DataMul.eq.MulData
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.Mul
import Lemma.Vector.EqMul0_0
import sympy.tensor.tensor
open Vector Tensor


@[main, subst 0]
private lemma main
  [MulZeroClass α]
  {s : List ℕ}
-- given
  (a : α) :
-- imply
  (0 : Tensor α s) * a = 0 := by
-- proof
  apply Eq.of.EqDataS
  rw [DataMul.eq.MulData]
  rw [EqData0'0]
  apply EqMul0_0


@[main]
private lemma nat
  [Semiring α]
  [CharZero α]
-- given
  (x : Tensor α []) :
-- imply
  (↑(0 : ℕ) : Tensor α []) * x = 0 := by
-- proof
  erw [Nat.cast_zero, Tensor.Mul]
  apply MulZeroClass.zero_mul


-- created on 2025-12-23
-- updated on 2026-09-04
