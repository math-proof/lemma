import sympy.Basic


@[main]
private lemma main
-- given
  (v : List.Vector α n)
  (i : Fin n) :
-- imply
  v.get i = v[i] := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-12
