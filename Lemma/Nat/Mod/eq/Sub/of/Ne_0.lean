import sympy.Basic


@[main]
private lemma main
  -- given
  (h : i ≠ 0)
  (n : ℕ) :
-- imply
  (n - i) % n = n - i := by
-- proof
  have : NeZero i := ⟨h⟩
  simp


-- created on 2025-10-18
