import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.Subset.is.SDiff.eq.Empty |
| comm | Set.SDiff.eq.Empty.is.Subset |
| mp | Set.SDiff.eq.Empty.of.Subset |
| mpr | Set.Subset.of.SDiff.eq.Empty |
-/
@[main, comm, mp, mpr]
private lemma main
  {A B : Set α} :
-- imply
  A ⊆ B ↔ A \ B = ∅ := by
-- proof
  constructor
  ·
    grind
  ·
    intro h x hx
    by_contra hnot
    have : x ∈ A \ B := ⟨hx, hnot⟩
    rwa [h] at this


-- created on 2018-03-03
