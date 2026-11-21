import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.EqGet1_1 |
| fin | Vector.EqGet1_1.fin |
| subst 1 | Vector.EqGet1_1.of.Eq_1 |
-/
@[path, fin, subst 1]
private lemma main
  [One α]
-- given
  (i : Fin n) :
-- imply
  (1 : List.Vector α n)[i] = 1 := by
-- proof
  simp [GetElem.getElem]
  erw [List.Vector.get_replicate]


-- created on 2025-09-23
-- updated on 2026-11-20
