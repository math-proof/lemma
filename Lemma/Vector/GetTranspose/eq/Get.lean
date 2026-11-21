import Def.Data.Vector.Basic.Part2
import Lemma.Vector.EqGetRange.of.Lt
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetTranspose.eq.Get |
| fin | Vector.GetTranspose.eq.Get.fin |
| val | Vector.GetTranspose.eq.Get.val |
-/
@[path, fin, val]
private lemma main
-- given
  (v : List.Vector (List.Vector α n) m)
  (i : Fin m)
  (j : Fin n) :
-- imply
  v.transpose[j, i] = v[i, j] := by
-- proof
  unfold List.Vector.transpose
  simp [EqGetRange.of.Lt]


-- created on 2025-06-15
-- updated on 2026-11-20
