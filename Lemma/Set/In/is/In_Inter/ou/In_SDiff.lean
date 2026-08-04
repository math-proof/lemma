import Lemma.Set.EqUnionInter__SDiff
import Lemma.Set.IffInS.of.Eq
import Lemma.Set.In_Union.is.OrInS
open Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Set.In.is.In_Inter.ou.In_SDiff |
| comm | Set.In_Inter.ou.In_SDiff.is.In |
| mp | Set.In_Inter.ou.In_SDiff.of.In |
| mpr | Set.In.of.In_Inter.ou.In_SDiff |
-/
@[main, comm, mp, mpr]
private lemma main
-- given
  (A B : Set α)
  (x : α) :
-- imply
  x ∈ A ↔ x ∈ A ∩ B ∨ x ∈ A \ B := by
-- proof
  have := EqUnionInter__SDiff (s := A) (t := B)
  have := IffInS.of.Eq this x
  rw [In_Union.is.OrInS] at this
  rwa [Iff.comm]


-- created on 2018-02-21
-- updated on 2025-05-01
