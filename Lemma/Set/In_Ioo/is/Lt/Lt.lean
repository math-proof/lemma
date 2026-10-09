import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.In_Ioo.is.Lt.Lt |
| comm | Set.Lt.Lt.is.In_Ioo |
| mp | Set.Lt.Lt.of.In_Ioo |
| mpr | Set.In_Ioo.of.Lt.Lt |
-/
@[path, comm, mp, mpr]
private lemma main
  [Preorder α]
-- given
  (a b : α) :
-- imply
  x ∈ Ioo a b ↔ a < x ∧ x < b := by
-- proof
  rfl


-- created on 2025-03-02
