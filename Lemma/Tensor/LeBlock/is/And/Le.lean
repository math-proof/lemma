import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ}
  {x : ℝ} :
-- imply
  (∀ i, Fin.append a b i ≤ x) ↔ (∀ i, a i ≤ x) ∧ (∀ i, b i ≤ x) := by
-- proof
  constructor
  · intro h
    constructor
    · intro i
      simpa using h (Fin.castAdd m i)
    · intro i
      simpa using h (Fin.natAdd n i)
  · rintro ⟨h₀, h₁⟩ i
    induction i using Fin.addCases with
    | left j =>
      simpa using h₀ j
    | right j =>
      simpa using h₁ j


-- created on 2022-04-01
