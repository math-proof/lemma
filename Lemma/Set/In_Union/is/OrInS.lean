import Lemma.Set.AndNotSIn.of.NotIn_Union
import Lemma.Bool.NotOr.is.AndNotS
open Set Bool


@[main, comm, mp, mpr]
private lemma fin
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι} :
-- imply
  e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B := by
-- proof
  constructor <;>
    intro h
  .
    rwa [Finset.mem_union] at h
  .
    by_contra h
    have := AndNotSIn.of.NotIn_Union.fin h
    rw [AndNotS.is.NotOr] at this
    contradiction


@[main, comm, mp, mpr]
private lemma main
  {A B : Set α}
  {e : α} :
-- imply
  e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B := by
-- proof
  constructor <;>
    intro h
  .
    rwa [Set.mem_union] at h
  .
    by_contra h
    have := AndNotSIn.of.NotIn_Union h
    contradiction


-- created on 2025-04-30
-- updated on 2025-05-01
