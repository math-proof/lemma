import sympy.Basic


@[main]
private lemma main
  {n u : ℕ}
  {A B : ℕ → ℕ → ℝ}
-- given
  (h : ∀ i < n - u, A i = B i) :
-- imply
  ∀ i < n - u, ∀ j < u, A i (i + j) = B i (i + j) := by
-- proof
  intro i hi j _
  rw [h i hi]


-- created on 2026-09-27
