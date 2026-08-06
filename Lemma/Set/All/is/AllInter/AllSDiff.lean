import Lemma.Set.AllIn_SDiff.of.All
import Lemma.Set.In.is.In_Inter.ou.In_SDiff
import Lemma.Set.In_Inter.is.In.In
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.All.is.AllInter.AllSDiff |
| comm | Set.AllInter.AllSDiff.is.All |
| mp | Set.AllInter.AllSDiff.of.All |
| mpr | Set.All.of.AllInter.AllSDiff |
-/
@[main, comm, mp, mpr]
private lemma main
  {A B : Set α}
  {f : α → Prop} :
-- imply
  (∀ x ∈ A, f x) ↔ (∀ x ∈ A ∩ B, f x) ∧ (∀ x ∈ A \ B, f x) := by
-- proof
  constructor
  · intro h
    constructor
    · intro x hx
      apply h
      exact (In.In.of.In_Inter hx).left
    · exact AllIn_SDiff.of.All h B
  · intro h x hx
    obtain ⟨h_inter, h_sdiff⟩ := h
    obtain h' | h' := In_Inter.ou.In_SDiff.of.In B hx
    · exact h_inter x h'
    · exact h_sdiff x h'


-- created on 2018-04-23
