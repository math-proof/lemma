import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.NotIn.is.In_SDiff |
| comm | Set.In_SDiff.is.NotIn |
| mp | Set.In_SDiff.of.NotIn |
| mpr | Set.NotIn.of.In_SDiff |
-/
@[main, comm, mp, mpr]
private lemma main
  {x : α}
  {s : Set α} :
-- imply
  x ∉ s ↔ x ∈ (Set.univ : Set α) \ s := by
-- proof
  constructor
  · exact Set.mem_sdiff_of_mem (Set.mem_univ _)
  · intro h
    exact h.right


-- created on 2023-05-21
