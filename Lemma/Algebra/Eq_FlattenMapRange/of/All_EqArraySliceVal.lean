import Lemma.Algebra.ValArraySlice.eq.ArraySliceVal
import Lemma.Algebra.Eq_FlattenMapRange.of.All_EqValS
open Algebra


@[main]
private lemma main
  {v : List.Vector α (m * n)}
  {u : Fin m → List.Vector α n}
-- given
  (h : ∀ i : Fin m, v.val.array_slice (i * n) n = (u i).val) :
-- imply
  v = ((List.Vector.range m).map fun i => u i).flatten := by
-- proof
  simp only [← ValArraySlice.eq.ArraySliceVal v] at h
  apply Eq_FlattenMapRange.of.All_EqValS h


-- created on 2025-05-18
