import Lemma.Vector.EqFlattenUnflatten
import Lemma.Vector.Eq_MapRange_FunGet
open Vector


@[main]
private lemma main
  {v : List.Vector α (m * n)}
  {u : Fin m → List.Vector α n}
-- given
  (h : ∀ i : Fin m, v.unflatten[i] = u i) :
-- imply
  ((List.Vector.range m).map fun i => u i).flatten = v:= by
-- proof
  simp only [← h]
  rw [← Eq_MapRange_FunGet v.unflatten]
  apply EqFlattenUnflatten


-- created on 2025-11-11
