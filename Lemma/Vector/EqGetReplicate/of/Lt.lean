import sympy.Basic


@[main]
private lemma main
-- given
  (h : i < n) :
-- imply
  (List.Vector.replicate n a)[i] = a := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-06
