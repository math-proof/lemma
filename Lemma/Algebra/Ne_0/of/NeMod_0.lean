import sympy.Basic


@[main]
private lemma main
  {n d : ℕ}
-- given
  (h₁ : n % d ≠ 0) :
-- imply
  n ≠ 0 := by
-- proof
  by_contra h'
  rw [h'] at h₁
  simp at h₁


-- created on 2025-06-16
