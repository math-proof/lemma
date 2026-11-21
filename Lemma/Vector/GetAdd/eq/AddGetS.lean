import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.GetAdd.eq.AddGetS |
| fin | Vector.GetAdd.eq.AddGetS.fin |
-/
@[path, fin]
private lemma main
  [Add α]
-- given
  (a b : List.Vector α n)
  (i : Fin n) :
-- imply
  (a + b)[i] = a[i] + b[i] := by
-- proof
  conv in a + b =>
    simp [HAdd.hAdd]
  simp [Add.add]
  simp [GetElem.getElem]


-- created on 2025-07-14
-- updated on 2026-11-20
