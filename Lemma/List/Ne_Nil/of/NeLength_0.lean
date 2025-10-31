import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length ≠ 0) :
-- imply
  s ≠ [] := by
-- proof
  by_contra h'
  rw [h'] at h
  simp at h


-- created on 2025-05-08
