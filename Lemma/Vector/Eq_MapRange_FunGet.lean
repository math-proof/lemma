import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
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
  grind


-- created on 2025-05-10
-- updated on 2025-10-25
