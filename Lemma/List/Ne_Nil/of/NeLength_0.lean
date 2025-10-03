import sympy.vector.vector
import sympy.Basic


@[main]
private lemma main
  {v : List α}
-- given
  (h : v.length ≠ 0) :
-- imply
  v ≠ [] := by
-- proof
  by_contra h'
  rw [h'] at h
  simp at h


-- created on 2025-05-08
