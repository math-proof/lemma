import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n m : ℕ}
  {x : ℝ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ} :
-- imply
  (∀ i, x ≤ Sum.elim a b i) ↔ (∀ i, x ≤ a i) ∧ (∀ j, x ≤ b j) := by
-- proof
  constructor
  ·
    intro h
    constructor
    ·
      intro i
      simpa using h (Sum.inl i)
    ·
      intro j
      simpa using h (Sum.inr j)
  ·
    intro h i
    cases i with
    | inl i =>
      simpa using h.1 i
    | inr j =>
      simpa using h.2 j


-- created on 2022-04-01
-- updated on 2026-10-26
