import sympy.vector.vector
import Lemma.List.GetElemRange.eq.Some.is.Lt.Eq
import Lemma.List.GetElem.eq.Some.is.Any_Eq
open List


@[main]
private lemma Main'
-- given
  (v : List.Vector α m) :
-- imply
  v = (List.Vector.range m).map fun i : Fin m => v[i] := by
-- proof
  simp [List.Vector.map]
  simp only [List.Vector.range]
  simp only [GetElem.getElem]
  simp only [List.Vector.get]
  simp_all [List.map_pmap]
  let ⟨v, h_length⟩ := v
  congr
  ext i a
  simp [GetElemRange.eq.Some.is.Lt.Eq]
  simp only [GetElem.eq.Some.is.Any_Eq]
  simp only [h_length]
  simp only [Eq.comm]


-- created on 2025-05-10
