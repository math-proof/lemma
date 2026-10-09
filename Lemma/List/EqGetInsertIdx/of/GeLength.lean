import sympy.Basic


@[path, fin]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ i)
  (a : α) :
-- imply
  (s.insertIdx i a)[i]'(by grind) = a := by
-- proof
  simp


-- created on 2025-10-03
