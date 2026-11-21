import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetDiv.eq.DivGet |
| fin | Vector.GetDiv.eq.DivGet.fin |
-/
@[path, fin]
private lemma main
  [Div α]
-- given
  (x : List.Vector α n)
  (a : α)
  (i : Fin n) :
-- imply
  (x / a)[i] = x[i] / a := by
-- proof
  simp [HDiv.hDiv]


-- created on 2025-09-22
-- updated on 2026-11-20
