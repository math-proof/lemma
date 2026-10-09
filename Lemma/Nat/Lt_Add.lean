import sympy.Basic


@[path]
private lemma main
-- given
  (i : Fin n)
  (m : ℕ) :
-- imply
  i < n + m := by
-- proof
  have := i.isLt
  linarith


-- created on 2025-05-30
