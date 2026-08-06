import sympy.Basic
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Insert.is.Eq.ou.In |
| comm | Set.Eq.ou.In.is.In_Insert |
| mp   | Set.Eq.ou.In.of.In_Insert |
| mpr  | Set.In_Insert.of.Eq.ou.In |
-/
@[main, comm, mp, mpr]
private lemma main
  {a e : α}
  {s : Set α} :
-- imply
  e ∈ insert a s ↔ e = a ∨ e ∈ s :=
-- proof
  mem_insert_iff


-- created on 2026-08-06
