import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s ≠ []) :
-- imply
  s.length > 0 := by
-- proof
  by_contra h'
  simp at h'
  contradiction


-- created on 2025-06-29
