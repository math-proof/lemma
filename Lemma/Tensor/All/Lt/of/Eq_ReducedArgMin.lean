import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℝ}
  {m : Fin n}
-- given
  (h₀ : ∀ j, x m ≤ x j)
  (h₁ : ∀ j, j < m → x j ≠ x m) :
-- imply
  ∀ k, k < m → x m < x k := by
-- proof
  intro k hk
  exact lt_of_le_of_ne (h₀ k) (Ne.symm (h₁ k hk))


-- created on 2023-11-05
-- updated on 2026-10-26
