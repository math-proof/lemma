import Lemma.Vector.GetRepeat.eq.Get_Mod
open Vector Nat


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetRepeat_AddMul.eq.Get.of.Eq_AddMul |
| fin | Vector.GetRepeat_AddMul.eq.Get.of.Eq_AddMul.fin |
-/
@[path, fin]
private lemma main
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector α n) :
-- imply
  (v.repeat m)[t]'(by convert AddMul.lt.Mul i j) = v[j] := by
-- proof
  simp [GetElem.getElem]
  simp [GetRepeat.eq.Get_Mod.fin]
  simp [h_t]
  simp [Nat.mod_eq_of_lt j.isLt]


-- created on 2025-09-24
-- updated on 2026-11-20
