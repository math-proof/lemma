import sympy.Basic


@[main, fin]
private lemma main
-- given
  (h : n = n')
  (v : List.Vector α n)
  (i : Fin n') :
-- imply
  (cast (congrArg (List.Vector α) h) v)[i] = v[i] := by
-- proof
  simp [GetElem.getElem]
  simp [List.Vector.get]
  aesop


-- created on 2025-07-06
