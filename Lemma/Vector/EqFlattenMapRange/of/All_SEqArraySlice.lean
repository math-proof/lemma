import Lemma.Bool.SEq.is.Eq
import Lemma.Vector.EqFlattenMapRange.of.All_EqGetUnflatten
import Lemma.Vector.GetUnflatten.as.ArraySlice
import sympy.vector.vector
open Bool Vector


@[main, comm]
private lemma main
  {v : List.Vector α (m * n)}
  {u : Fin m → List.Vector α n}
-- given
  (h : ∀ i : Fin m, v.array_slice (i * n) n ≃ u i) :
-- imply
  ((List.Vector.range m).map fun i => u i).flatten = v := by
-- proof
  apply EqFlattenMapRange.of.All_EqGetUnflatten
  intro i
  have := GetUnflatten.as.ArraySlice v i
  have h := h i
  have h := this.trans h
  apply Eq.of.SEq h


-- created on 2025-11-11
