import sympy.Basic


@[main]
private lemma main
  {p q : α → ι → Prop}
-- given
  (h₀ : ∀ x : α, ∀ i : ι, p x i)
  (h₁ : ∀ x : α, ∃ j : ι, q x j) :
-- imply
  ∀ x : α, ∃ j, ∀ i : ι, p x i ∧ q x j := by
-- proof
  intro x                  -- Fix arbitrary x : α
  obtain ⟨j₀, hq⟩ := h₁ x  -- Use h₁ to get j₀ such that q x j₀
  use j₀                   -- Use j₀ as our witness
  intro i                  -- Fix arbitrary i : ι
  constructor              -- Split the conjunction
  · exact h₀ x i           -- Prove p x i using h₀
  · exact hq               -- Prove q x j₀ (hq)


-- created on 2025-07-19
