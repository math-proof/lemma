import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Supset.is.All_In |
| comm | Set.All_In.is.Supset |
| mp | Set.All_In.of.Supset |
| mpr | Set.Supset.of.All_In |
-/
@[main, comm, mp, mpr]
private lemma main
  {A B : Set α} :
-- imply
  A ⊇ B ↔ ∀ x ∈ B, x ∈ A :=
-- proof
  Iff.rfl


-- created on 2018-03-30
