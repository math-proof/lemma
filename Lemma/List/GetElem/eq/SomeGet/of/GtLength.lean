import stdlib.List
import sympy.Basic


@[path]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s[i]? = some s[i] := by
-- proof
  simp [h]


-- created on 2025-05-15
