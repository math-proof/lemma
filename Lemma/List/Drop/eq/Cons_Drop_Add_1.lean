import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  s.drop i = s[i] :: s.drop (i + 1) := by
-- proof
  simp


-- created on 2025-06-08
