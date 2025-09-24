import sympy.tensor.Basic
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Algebra.EqMulDiv.of.Dvd
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Algebra.EqMod_1'0
import Lemma.Vector.Head.eq.Get_0
open Vector Algebra


@[main]
private lemma main
  [Div α]
-- given
  (X : Tensor α s)
  (A : Tensor α []) :
-- imply
  X / A = X / A.broadcast s (by simp) := by
-- proof
  simp [HDiv.hDiv]
  simp [Div.div]
  simp [HDiv.hDiv]
  simp [Div.div]
  let ⟨X⟩ := X
  simp
  simp [Tensor.broadcast]
  let ⟨A⟩ := A
  simp
  ext i
  simp
  rw [GetCast.eq.Get.of.Eq.fin]
  ·
    rw [GetRepeat.eq.Get_Mod.fin]
    simp [EqMod_1'0]
    rw [Head.eq.Get_0]
    simp [HDiv.hDiv]
  ·
    rw [EqMulDiv.of.Dvd]
    simp


-- created on 2025-09-24
