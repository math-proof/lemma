import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {x : ℝ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ} :
-- imply
  (∀ i, x ≤ Sum.elim a b i) → (∀ i, x ≤ a i) ∧ (∀ j, x ≤ b j) := by
-- proof
  intro h
  constructor
  ·
    intro i
    simpa using h (Sum.inl i)
  ·
    intro j
    simpa using h (Sum.inr j)


-- created on 2026-10-11
-- updated on 2026-10-17
