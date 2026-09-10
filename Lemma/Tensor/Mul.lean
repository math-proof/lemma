import Lemma.Nat.Mul
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.Map₂.eq.Map.of.Eq_1
import sympy.tensor.Basic
open Tensor Vector


@[main]
private lemma main
  [Mul α]
-- given
  (X Y : Tensor α []) :
-- imply
  X * Y = Mul.mul X Y := by
-- proof
  apply Eq.of.EqDataS
  simp [HMul.hMul, Mul.mul]
  erw [Map₂.eq.Map.of.Eq_1 (n := [].prod) (by rfl)]
  rfl


@[main]
private lemma Comm
  [CommMagma α]
-- given
  (X Y : Tensor α []) :
-- imply
  Mul.mul X Y = Mul.mul Y X := by
-- proof
  apply Eq.of.EqDataS
  ext i
  simp [Mul.mul]
  erw [GetMul.eq.MulGetS.fin (a := X.data) (b := Y.data) (i := i)]
  erw [GetMul.eq.MulGetS.fin (a := Y.data) (b := X.data) (i := i)]
  rw [Nat.Mul.comm]


@[main, comm]
private lemma nat
  [Semiring α]
  [CharZero α]
-- given
  (x : Tensor α [])
  (n : ℕ) :
-- imply
  x * (n : Tensor α []) = (n : Tensor α []) * x := by
-- proof
  repeat rw [main]
  apply Eq.of.EqDataS
  ext i
  simp only [Mul.mul]
  repeat rw [GetMul.eq.MulGetS.fin]
  have hn : (n : Tensor α []).data.get i = (n : α) := by
    fin_cases i
    rfl
  rw [hn]
  exact (Nat.cast_commute n _).symm.eq


-- created on 2026-09-02
-- updated on 2026-09-10
