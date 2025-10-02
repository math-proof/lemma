import sympy.vector.vector
import Lemma.Algebra.GetElem!Range.eq.Some.is.Lt.Eq
import Lemma.Algebra.GetElem!.eq.Some.is.Any_Eq
open Algebra


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
  simp [GetElem!Range.eq.Some.is.Lt.Eq]
  simp only [GetElem!.eq.Some.is.Any_Eq]
  simp only [h_length]
  simp only [Eq.comm]


-- created on 2025-05-10
