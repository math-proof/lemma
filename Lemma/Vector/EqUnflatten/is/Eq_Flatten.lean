import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.EqUnflattenFlatten
open Vector


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
-- given
  (v : List.Vector α (m * n))
  (u : List.Vector (List.Vector α n) m) :
-- imply
  v.unflatten = u ↔ v = u.flatten := by
-- proof
  constructor <;> 
    intro h
  ·
    rw [← h]
    rw [EqFlattenUnflatten]
  ·
    rw [h]
    rw [EqUnflattenFlatten]


-- created on 2025-11-14
