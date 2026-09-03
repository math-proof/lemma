import Lemma.Nat.Mul
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Vector.GetMul.eq.MulGetS
import Lemma.Vector.Map₂.eq.Map.of.Eq_1
import sympy.tensor.Basic
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.Mul |
| comm | Tensor.Mul.comm |
-/
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


-- created on 2026-09-02
-- updated on 2026-09-03
