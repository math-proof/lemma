import Lemma.Nat.EqAddMulDiv
import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Vector.EqGet0_0
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetRepeat.eq.Get_Mod
import sympy.vector.vector
open Nat Vector


@[main, fin]
private lemma main
  [Zero α]
-- given
  (v : List.Vector α m)
  (n : ℕ)
  (i : Fin n) :
-- imply
  (v.resize n)[i] = if h : i < n / m * m then
    v[i % m]'(LtMod.of.Lt_Mul h)
  else
    0 := by
-- proof
  simp [GetElem.getElem]
  unfold List.Vector.resize
  split_ifs with h
  ·
    rw [GetCast.eq.Get.of.Eq.fin (by simp [EqAddMulDiv])]
    rw [GetAppend.eq.Get.of.Lt.fin (by grind)]
    rw [GetRepeat.eq.Get_Mod.fin]
  ·
    rw [GetCast.eq.Get.of.Eq.fin (by simp [EqAddMulDiv])]
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind)]
    apply EqGet0_0.fin


-- created on 2026-07-13
