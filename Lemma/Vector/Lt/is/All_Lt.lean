import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Lt.is.All_Lt |
| comm | Vector.All_Lt.is.Lt |
| mp | Vector.All_Lt.of.Lt |
| mpr | Vector.Lt.of.All_Lt |
-/
@[path, comm, mp, mpr]
private lemma main
  [LT α]
-- given
  (a b : List.Vector α n) :
-- imply
  a < b ↔ ∀ i : Fin n, a[i] < b[i] := by
-- proof
  rfl


-- created on 2026-07-27
-- updated on 2026-11-20
