import sympy.Basic


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s ≠ [])
  (n : ℕ)
  (x : α) :
-- imply
  (s.insertIdx (n + 1) x).tail = s.tail.insertIdx n x := by
-- proof
  cases s <;>
    simp_all


-- created on 2025-07-13
