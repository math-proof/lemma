import sympy.vector.vector
import sympy.Basic


@[path, fin, val]
private lemma main
  {n : ℕ}
-- given
  (i : Fin n) :
-- imply
  (List.Vector.range n)[i] = i := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.range]
  simp [List.Vector.get]


-- created on 2025-05-18
