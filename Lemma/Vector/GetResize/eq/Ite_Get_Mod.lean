import Theorem.Vector.EqGet0_0
import Lemma.Vector.GetAppend.eq.Get.of.Lt
import Lemma.Vector.GetAppend.eq.Get_Sub.of.Lt_Add.Ge
import Lemma.Vector.GetCast.eq.Get.of.Eq
import Lemma.Vector.GetRepeat.eq.Get_Mod
open Nat Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetResize.eq.Ite_Get_Mod |
| fin | Vector.GetResize.eq.Ite_Get_Mod.fin |
-/
@[path, fin]
private lemma main
  [Zero α]
-- given
  (v : List.Vector α m)
  (n : ℕ)
  (i : Fin n) :
-- imply
  (v.resize n)[i] = if h : i < n / m * m then
    v[i % m]'(Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h)))
  else
    0 := by
-- proof
  simp [GetElem.getElem]
  unfold List.Vector.resize
  split_ifs
  <;> rw [GetCast.eq.Get.of.Eq.fin (by simp [EqAddMulDiv])]
  ·
    rw [GetAppend.eq.Get.of.Lt.fin (by grind)]
    rw [GetRepeat.eq.Get_Mod.fin]
  ·
    rw [GetAppend.eq.Get_Sub.of.Lt_Add.Ge.fin (by grind)]
    apply EqGet0_0.fin


-- created on 2026-07-13
-- updated on 2026-11-20
