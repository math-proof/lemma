import sympy.Basic


@[path]
private lemma main
  {P : ℕ → Prop}
  {m n : ℕ}
-- given
  (hmn : m ≤ n)
  (h₀ : P m)
  (h₁ : P (m + 1))
  (h : ∀ k, P k ∧ P (k + 1) → P (k + 2)) :
-- imply
  P n := by
-- proof
  have hstep : ∀ d : ℕ, P (m + d) ∧ P (m + d + 1) := by
    intro d
    induction d with
    | zero =>
      exact ⟨h₀, h₁⟩
    | succ d ih =>
      exact ⟨ih.2, h (m + d) ⟨ih.1, ih.2⟩⟩
  have hnm : m + (n - m) = n := by
    omega
  rw [← hnm]
  exact (hstep (n - m)).1


-- created on 2019-03-14
-- updated on 2023-05-20
