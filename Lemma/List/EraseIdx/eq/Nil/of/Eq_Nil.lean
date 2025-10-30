import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s = []) :
-- imply
  s.eraseIdx i = [] := by
-- proof
  simp_all


-- created on 2025-06-24
