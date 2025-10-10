import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s ≠ [])
  (i : ℕ)
  (a : α) :
-- imply
  s.set i a ≠ [] := by
-- proof
  aesop


-- created on 2025-10-10
