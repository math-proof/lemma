import sympy.Basic


@[main]
private lemma main
  {a : List α}
-- given
  (h : i < a.length)
  (b : List α) :
-- imply
  (a ++ b).eraseIdx i = a.eraseIdx i ++ b := by
-- proof
  grind


-- created on 2025-10-31
