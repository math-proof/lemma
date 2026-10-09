import sympy.Basic


@[path, comm]
private lemma main
-- given
  (s : List ℕ) :
-- imply
  s.eraseIdx (s.length - 1) = s.dropLast := by
-- proof
  simp


-- created on 2025-11-24
