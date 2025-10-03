import stdlib.List
import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : i < a.length) :
-- imply
  a[i]? = some a[i] := by
-- proof
  simp [h]


-- created on 2025-05-15
