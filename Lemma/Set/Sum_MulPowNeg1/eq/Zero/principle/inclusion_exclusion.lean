import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
-- given
  (h₀ : n ≠ 0) :
-- imply
  ∑ k ∈ Finset.range (n + 1), (-1) ^ (n - k) * (Nat.choose n k : ℤ) = 0 := by
-- proof
  have h := add_pow (1 : ℤ) (-1) n
  have hzero : ((1 : ℤ) + -1) ^ n = 0 := by
    simp [h₀]
  rw [hzero] at h
  simpa [one_pow, mul_one] using h.symm


-- created on 2021-04-23
-- updated on 2026-10-26
