import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n m : ℕ}
  {x : ℝ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ} :
-- imply
  (∀ i, a i < x) ∧ (∀ j, b j < x) → (∀ i, Sum.elim a b i < x) := by
-- proof
  intro h i
  cases i with
  | inl i =>
    simpa using h.1 i
  | inr j =>
    simpa using h.2 j


-- created on 2022-04-01
-- updated on 2026-10-26
