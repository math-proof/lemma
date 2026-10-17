import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : ℕ → α}
-- given
  (h₀ : ∀ i < n, ∀ j < i, x j ≠ x i)
  (h₁ : ∀ i < n, x n ≠ x i) :
-- imply
  ∀ i ≤ n, ∀ j < i, x i ≠ x j := by
-- proof
  intro i hi j hj
  if hin : i < n then
    exact (h₀ i hin j hj).symm
  else
    have hi_eq : i = n := by omega
    rw [hi_eq] at hj ⊢
    exact h₁ j hj


-- created on 2026-10-11
-- updated on 2026-10-17
