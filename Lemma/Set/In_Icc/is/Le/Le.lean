import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Icc.is.Le.Le |
| comm | Set.Le.Le.is.In_Icc |
| mp | Set.Le.Le.of.In_Icc |
| mpr | Set.In_Icc.of.Le.Le |
-/
@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (a b : α) :
-- imply
  x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b := by
-- proof
  rfl


-- created on 2025-04-27
