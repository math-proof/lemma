import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_SetOf.is.In.UFn |
| comm | Set.In.UFn.is.In_SetOf |
| mp | Set.In.UFn.of.In_SetOf |
| mpr | Set.In_SetOf.of.In.UFn |
-/
@[main, comm, mp, mpr]
private lemma main
  {x : α}
  {s : Set α}
  {f : α → Prop} :
-- imply
  x ∈ {a ∈ s | f a} ↔ x ∈ s ∧ f x :=
-- proof
  Iff.rfl


-- created on 2018-11-19
-- updated on 2026-08-28
