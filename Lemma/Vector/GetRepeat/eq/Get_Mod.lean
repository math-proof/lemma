import Def.Data.Vector.Basic.Part2
import Theorem.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
open Vector Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetRepeat.eq.Get_Mod |
| fin | Vector.GetRepeat.eq.Get_Mod.fin |
| val | Vector.GetRepeat.eq.Get_Mod.val |
-/
@[path, fin, val]
private lemma main
-- given
  (x : List.Vector α n)
  (k : Fin (m * n)) :
-- imply
  (x.repeat m)[k] = x[k % n]'(Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simpa using k.isLt))) := by
-- proof
  let ⟨i, j, h_ij⟩ := Fin.Any_Eq_AddMul.of.Lt_Mul k.isLt
  unfold List.Vector.repeat
  simp [h_ij]
  simp [GetElem.getElem]
  rw [GetFlatten_AddMul.eq.Get.fin]
  simp [Nat.mod_eq_of_lt j.isLt]


-- created on 2025-09-24
-- updated on 2026-11-20
