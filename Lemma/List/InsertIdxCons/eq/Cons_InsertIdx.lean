import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (x s₀ : α)
  (n : ℕ) :
-- imply
  (s₀ :: s).insertIdx (n + 1) x = s₀ :: s.insertIdx n x := by
-- proof
  cases n <;> rfl


-- created on 2025-06-09
