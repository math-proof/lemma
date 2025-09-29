import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  [Preorder α]
  {a b : α}
  {g : α → Prop}
-- given
  (h₀ : a ≤ b)
  (h : ∀ k ∈ Icc a b, g k) :
-- imply
  ∀ k ∈ Ico a b, g k ∧ g b := by
-- proof
  intro k hk
  -- Split hk into a ≤ k and k < b
  rcases hk with ⟨ha, hb⟩
  -- g k holds because k ∈ Icc a b (using k < b → k ≤ b)
  have g_k : g k := h k ⟨ha, le_of_lt hb⟩
  -- g b holds because b ∈ Icc a b (h₀ and reflexivity)
  have g_b : g b := h b ⟨h₀, le_refl b⟩
  -- Combine both proofs
  exact ⟨g_k, g_b⟩


-- created on 2025-07-20
