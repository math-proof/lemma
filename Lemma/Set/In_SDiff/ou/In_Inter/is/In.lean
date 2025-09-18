import Lemma.Set.In.is.In_Inter.ou.In_SDiff
open Set


@[main]
private lemma fin
  [DecidableEq ι]
  {A B : Finset ι}
  {x : ι} :
-- imply
  x ∈ A \ B ∨ x ∈ A ∩ B ↔ x ∈ A := by
-- proof
  rw [Iff.comm]
  rw [Or.comm]
  apply In.is.In_Inter.ou.In_SDiff.fin


@[main]
private lemma main
  {A B : Set α}
  {x : α} :
-- imply
  x ∈ A \ B ∨ x ∈ A ∩ B ↔ x ∈ A := by
-- proof
  rw [Iff.comm]
  rw [Or.comm]
  apply In.is.In_Inter.ou.In_SDiff


-- created on 2025-04-30
-- updated on 2025-05-01
