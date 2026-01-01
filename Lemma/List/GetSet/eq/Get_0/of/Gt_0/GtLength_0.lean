import sympy.Basic


@[main, fin]
private lemma main
  {x : List α}
-- given
  (h_x : x.length > 0)
  (h : d > 0)
  (a : α) :
-- imply
  (x.set d a)[0]'(by grind) = x[0] := by
-- proof
  grind


-- created on 2025-07-17
