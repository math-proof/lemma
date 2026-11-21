import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetAdd.eq.AddGet |
| fin | Vector.GetAdd.eq.AddGet.fin |
-/
@[path, fin]
private lemma main
  [Add α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x + a)[i] = x[i] + a := by
-- proof
  simp [HAdd.hAdd]


-- created on 2025-11-30
-- updated on 2026-11-20
