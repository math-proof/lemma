import Def.Data.Vector.Basic
import Instance.Data.Vector.Vector


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.EqGetRange |
| fin | Vector.EqGetRange.fin |
| val | Vector.EqGetRange.val |
-/
@[path, fin, val]
private lemma main
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n)[i] = i := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.range]
  simp [List.Vector.get]


-- created on 2025-05-18
-- updated on 2026-11-20
