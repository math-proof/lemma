import sympy.Basic


@[main]
private lemma left
-- given
  (h₀ : p → q)
  (h₁ : p ∧ r) :
-- imply
  q ∧ r := by
-- proof
  -- Split the conjunction h₀ into its components r and p
  let ⟨hp, hr⟩ := h₁
  -- Apply the implication h₁ to hp to get q
  have hq := h₀ hp
  -- Combine hr and hq to form the conjunction r ∧ q
  exact ⟨hq, hr⟩


@[main]
private lemma main
-- given
  (h₀ : p → q)
  (h₁ : r ∧ p) :
-- imply
  r ∧ q := by
-- proof
  -- Split the conjunction h₀ into its components r and p
  let ⟨hr, hp⟩ := h₁
  -- Apply the implication h₁ to hp to get q
  have hq := h₀ hp
  -- Combine hr and hq to form the conjunction r ∧ q
  exact ⟨hr, hq⟩


-- created on 2025-04-12
