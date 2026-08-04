import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Subset.is.All_In |
| comm | Set.All_In.is.Subset |
| mp | Set.All_In.of.Subset |
| mpr | Set.Subset.of.All_In |
-/
@[main, comm, mp, mpr]
private lemma main
  {A B : Set α} :
-- imply
  A ⊆ B ↔ ∀ x ∈ A, x ∈ B :=
-- proof
  Iff.of_eq Set.subset_def


-- created on 2018-03-27
