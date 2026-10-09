import sympy.vector.vector
import sympy.Basic


@[path, fin]
private lemma main
-- given
  (h_j : j < m - n)
  (v : List.Vector α m) :
-- imply
  (v.drop n)[j] = v[n + j] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  simp [List.Vector.drop]
  cases v
  simp


-- created on 2025-05-31
