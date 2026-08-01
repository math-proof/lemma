import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Finset.In_Inter.is.In.In |
| comm | Finset.In.In.is.In_Inter |
| mp | Finset.In.In.of.In_Inter |
| mpr | Finset.In_Inter.of.In.In |
-/
@[main, comm, mp, mpr]
private lemma main
  [DecidableEq ι]
-- given
  (e : ι)
  (A B : Finset ι) :
-- imply
  e ∈ A ∩ B ↔ e ∈ A ∧ e ∈ B :=
-- proof
  Finset.mem_inter


-- created on 2025-12-30
