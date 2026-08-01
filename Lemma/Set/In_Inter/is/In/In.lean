import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Inter.is.In.In |
| comm | Set.In.In.is.In_Inter |
| mp | Set.In.In.of.In_Inter |
| mpr | Set.In_Inter.of.In.In |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (e : α)
  (A B : Set α) :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Set.mem_inter_iff e A B


-- created on 2025-05-01
