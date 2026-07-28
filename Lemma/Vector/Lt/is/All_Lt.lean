import sympy.vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Lt.is.All_Lt |
| comm | Vector.All_Lt.is.Lt |
| mp | Vector.All_Lt.of.Lt |
| mpr | Vector.Lt.of.All_Lt |
-/
@[main, comm, mp, mpr]
private lemma main
  [LT α]
-- given
  (a b : List.Vector α n) :
-- imply
  a < b ↔ ∀ i : Fin n, a[i] < b[i] := by
-- proof
  rfl


-- created on 2026-07-27
