import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.EqGet0_0 |
| val | Vector.EqGet0_0.val |
| fin | Vector.EqGet0_0.fin |
| subst 0 | Vector.EqGet0_0.of.Eq_0 |
-/
@[path, val, fin, subst 0]
private lemma main
  [Zero α]
-- given
  (i : Fin n) :
-- imply
  (0 : List.Vector α n)[i] = 0 := by
-- proof
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]


-- created on 2025-09-04
-- updated on 2026-11-20
