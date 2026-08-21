import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Finset.is.OrEqS |
| comm | Set.OrEqS.is.In_Finset |
| mp | Set.OrEqS.of.In_Finset |
| mpr | Set.In_Finset.of.OrEqS |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (a b e : α) :
-- imply
  e ∈ ({a, b} : Set α) ↔ e = a ∨ e = b := by
-- proof
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]


-- created on 2018-11-18
-- updated on 2026-08-21
