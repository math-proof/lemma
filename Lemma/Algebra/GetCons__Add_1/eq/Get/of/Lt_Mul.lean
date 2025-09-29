import stdlib.List.Vector
import sympy.Basic


@[main]
private lemma main
-- given
  (h : i < m)
  (head : List.Vector α n)
  (tail : List.Vector (List.Vector α n) m):
-- imply
  (head ::ᵥ tail)[i + 1] = tail[i] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.cons]
  let ⟨tail, _⟩ := tail
  simp [List.Vector.get]


-- created on 2025-05-31
