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
  let ⟨ha, hb⟩ := hk
  have g_k : g k := h k ⟨ha, le_of_lt hb⟩
  have g_b : g b := h b ⟨h₀, le_refl b⟩
  exact ⟨g_k, g_b⟩


-- created on 2025-07-20
