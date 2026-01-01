import sympy.Basic
import sympy.vector.functions


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Setoid.is.All_SetoidGetS |
| comm | Vector.All_SetoidGetS.is.Setoid |
| mp | Vector.All_SetoidGetS.of.Setoid |
| mpr | Vector.Setoid.of.All_SetoidGetS |
| fin | Vector.Setoid.is.All_SetoidGetS.fin |
| fin.comm | Vector.All_SetoidGetS.is.Setoid.fin |
| fin.mp | Vector.All_SetoidGetS.of.Setoid.fin |
| fin.mpr | Vector.Setoid.of.All_SetoidGetS.fin |
-/
@[main, comm, mp, mpr, fin, fin.comm, fin.mp, fin.mpr]
private lemma main
  [Setoid α]
-- given
  (a b : List.Vector α n) :
-- imply
  a ≈ b ↔ ∀ i : Fin n, a[i] ≈ b[i] := by
-- proof
  aesop


-- created on 2025-12-23
