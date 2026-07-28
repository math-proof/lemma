import sympy.vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.Le.is.All_Le |
| comm | Vector.All_Le.is.Le |
| mp | Vector.All_Le.of.Le |
| mpr | Vector.Le.of.All_Le |
-/
@[main, comm, mp, mpr]
private lemma main
  [LE α]
-- given
  (a b : List.Vector α n) :
-- imply
  a ≤ b ↔ ∀ i : Fin n, a[i] ≤ b[i] := by
-- proof
  rfl


-- created on 2026-07-27
