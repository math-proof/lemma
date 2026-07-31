import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.EqUnflattenFlatten
open Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Vector.EqUnflatten.is.Eq_Flatten |
| comm | Vector.Eq_Flatten.is.EqUnflatten |
| mp | Vector.Eq_Flatten.of.EqUnflatten |
| mpr | Vector.EqUnflatten.of.Eq_Flatten |
| mp.comm | Vector.EqFlatten.of.Eq_Unflatten |
| mpr.comm | Vector.Eq_Unflatten.of.EqFlatten |
| comm.is | Vector.Eq_Unflatten.is.EqFlatten |
-/
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
