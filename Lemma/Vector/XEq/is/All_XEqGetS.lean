import sympy.Basic
import sympy.vector.functions


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.XEq.is.All_XEqGetS |
| comm | Vector.All_XEqGetS.is.XEq |
| mp | Vector.All_XEqGetS.of.XEq |
| mpr | Vector.XEq.of.All_XEqGetS |
| fin | Vector.XEq.is.All_XEqGetS.fin |
| fin.comm | Vector.All_XEqGetS.is.XEq.fin |
| fin.mp | Vector.All_XEqGetS.of.XEq.fin |
| fin.mpr | Vector.XEq.of.All_XEqGetS.fin |
-/
@[main, comm, mp, mpr, fin, fin.comm, fin.mp, fin.mpr]
private lemma main
  [XEq α]
-- given
  (a b : List.Vector α n) :
-- imply
  a ≈ b ↔ ∀ i : Fin n, a[i] ≈ b[i] := by
-- proof
  aesop


-- created on 2025-12-23
