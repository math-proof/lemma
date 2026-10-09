import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  {a : Fin n → ℝ}
  {b : Fin m → ℝ}
  {x : ℝ}
-- given
  (h₀ : ∀ i, a i ≤ x)
  (h₁ : ∀ i, b i ≤ x) :
-- imply
  ∀ i, Fin.append a b i ≤ x := by
-- proof
  intro i
  induction i using Fin.addCases with
  | left j =>
    simpa using h₀ j
  | right j =>
    simpa using h₁ j


-- created on 2022-04-01
