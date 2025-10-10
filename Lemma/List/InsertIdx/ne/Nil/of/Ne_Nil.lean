import sympy.Basic


@[main]
private lemma main
  {s : List α}
-- given
  (h : s ≠ [])
  (i : ℕ)
  (a : α) :
-- imply
  s.insertIdx i a ≠ [] := by
-- proof
  cases s with
  | nil =>
    aesop
  | cons =>
    cases i <;>
      simp


-- created on 2025-10-10
