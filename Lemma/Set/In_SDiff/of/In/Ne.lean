import sympy.Basic


@[main]
private lemma main
  {x y : α}
  {s : Set α}
-- given
  (h₀ : x ∈ s)
  (h₁ : x ≠ y) :
-- imply
  x ∈ s \ {y} := by
-- proof
  -- Split the goal into two parts: x ∈ s and x ∉ {y}
  constructor
    -- Prove x ∈ s using the hypothesis h₀
  exact h₀
    -- Prove x ∉ {y} using the hypothesis h₁ (since x ≠ y implies x ∉ {y})
  exact h₁


-- created on 2025-04-04
