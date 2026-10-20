import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Set.In_SDiff.is.And_NotIn |
| comm | Set.And_NotIn.is.In_SDiff |
| mp | Set.And_NotIn.of.In_SDiff |
| mpr | Set.In_SDiff.of.And_NotIn |
-/
@[path, comm, mp, mpr]
private lemma main
  {x : α}
  {A B : Set α} :
-- imply
  x ∈ B \ A ↔ x ∈ B ∧ x ∉ A := by
-- proof
  simp [Set.mem_sdiff]


-- created on 2021-01-25
-- updated on 2026-10-17
