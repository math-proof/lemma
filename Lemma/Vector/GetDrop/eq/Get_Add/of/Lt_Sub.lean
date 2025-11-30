import sympy.vector.vector
import sympy.Basic


@[main]
private lemma fin
-- given
  (h_j : j < m - n)
  (v : List.Vector α m) :
-- imply
  (v.drop n).get ⟨j, by omega⟩ = v.get ⟨n + j, by omega⟩ := by
-- proof
  simp [List.Vector.get]
  simp [List.Vector.drop]
  cases v
  simp


@[main]
private lemma main
-- given
  (h_j : j < m - n)
  (v : List.Vector α m) :
-- imply
  (v.drop n)[j] = v[n + j] := by
-- proof
  apply fin


-- created on 2025-05-31
