import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_Range.is.Any_Eq |
| comm | Set.Any_Eq.is.In_Range |
| mp | Set.Any_Eq.of.In_Range |
| mpr | Set.In_Range.of.Any_Eq |
-/
@[main, comm, mp, mpr]
private lemma main
  {ι : Sort u} {α : Type v} {f : ι → α} {a : α} :
-- imply
  a ∈ Set.range f ↔ ∃ x, f x = a :=
-- proof
  Iff.rfl


-- created on 2026-09-10
