import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.LtGetS.of.Lt |
| fin | Vector.LtGetS.of.Lt.fin |
-/
@[path, fin]
private lemma main
  [LT α]
  {a b : List.Vector α n}
-- given
  (h : a < b)
  (i : Fin n) :
-- imply
  a[i] < b[i] :=
-- proof
  h i


-- created on 2026-07-27
-- updated on 2026-11-20
