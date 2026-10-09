import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ}
  {x : ℝ}
-- given
  (h₀ : ∀ i, x ≥ a i)
  (h₁ : ∀ i, x ≥ b i) :
-- imply
  ∀ i, x ≥ Fin.append a b i := by
-- proof
  intro i
  induction i using Fin.addCases with
  | left j =>
    simpa using h₀ j
  | right j =>
    simpa using h₁ j


-- created on 2022-04-01
