import Lemma.Bool.NotOr.is.AndNotS
import Lemma.Finset.AndNotSIn.of.NotIn_Union
import Lemma.Set.AndNotSIn.of.NotIn_Union
open Set Bool Finset


@[main, comm, mp, mpr]
private lemma main
  [DecidableEq ι]
  {A B : Finset ι}
  {e : ι} :
-- imply
  e ∈ A ∪ B ↔ e ∈ A ∨ e ∈ B := by
-- proof
  constructor <;> 
    intro h
  ·
    rwa [Finset.mem_union] at h
  ·
    by_contra h
    have := AndNotSIn.of.NotIn_Union h
    rw [AndNotS.is.NotOr] at this
    contradiction


-- created on 2025-12-30
