import sympy.Basic


@[path]
private lemma main
  {n l u i : ℕ}
-- given
  (h₀ : i < min l n)
  (h₁ : l ≤ n) :
-- imply
  i < n ∧ i + 1 ≤ n + u := by
-- proof
  constructor
  ·
    omega
  ·
    omega


-- created on 2026-10-11
-- updated on 2026-10-17
