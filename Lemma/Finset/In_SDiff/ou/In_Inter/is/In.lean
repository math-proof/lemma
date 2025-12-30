import Lemma.Finset.In.is.In_Inter.ou.In_SDiff
open Finset


@[main]
private lemma main
  [DecidableEq ι]
  {A B : Finset ι}
  {x : ι} :
-- imply
  x ∈ A \ B ∨ x ∈ A ∩ B ↔ x ∈ A := by
-- proof
  rw [Iff.comm]
  rw [Or.comm]
  apply In.is.In_Inter.ou.In_SDiff


-- created on 2025-12-30
