import Def.Data.Vector.Basic
import Lemma.Vector.GetTake.eq.Get.of.Lt_Min
import Lemma.Vector.GetDrop.eq.Get_Add.of.Lt_Sub
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub |
| fin | Vector.GetArraySlice.eq.Get_Add.of.Lt_Min_Sub.fin |
-/
@[path, fin]
private lemma main
-- given
  (h : j < n ⊓ (N - i))
  (v : List.Vector α N) :
-- imply
  (v.array_slice i n)[j] = v[i + j] := by
-- proof
  simp [List.Vector.array_slice]
  simp only [GetTake.eq.Get.of.Lt_Min h]
  simp [GetElem.getElem]
  have := lt_of_lt_of_le h (min_le_right n (N - i))
  have := GetDrop.eq.Get_Add.of.Lt_Sub this v
  simp [GetElem.getElem] at this
  assumption


-- created on 2025-05-31
-- updated on 2026-11-21
