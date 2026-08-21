import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Singleton.is.Eq |
| comm | Set.Eq.is.In_Singleton |
| mp | Set.Eq.of.In_Singleton |
| mpr | Set.In_Singleton.of.Eq |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (a x : α) :
-- imply
  x ∈ ({a} : Set α) ↔ x = a :=
-- proof
  Set.mem_singleton_iff


-- created on 2018-10-23
-- updated on 2026-08-21
