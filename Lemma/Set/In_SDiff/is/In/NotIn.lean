import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In_SDiff.is.In.NotIn |
| comm | Set.In.NotIn.is.In_SDiff |
| mp | Set.In.NotIn.of.In_SDiff |
| mpr | Set.In_SDiff.of.In.NotIn |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (x : α)
  (A B : Set α) :
-- imply
  x ∈ A \ B ↔ x ∈ A ∧ x ∉ B := by
-- proof
  simp_all


-- created on 2025-05-18
