import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (i : Fin s.length) :
-- imply
  s.get i = s[i] := by
-- proof
  simp only [GetElem.getElem]


-- created on 2025-11-29
