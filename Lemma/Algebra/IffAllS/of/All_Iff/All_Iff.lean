import stdlib.List
import Lemma.Basic


@[main]
private lemma main
-- given
  (h₀ : ∀ a b : ℕ, a - 1 ≤ b ↔ a ≤ b + 1)
  (h₁ : ∀ a b : ℕ, a ≤ b ↔ ∀ c, c < a → c < b) :
-- imply
  (∀ b, a - 1 ≤ b) ↔ ∀ b c : ℕ, c < a → c < b + 1 := by
-- proof
  simp_rw [h₀, h₁]


-- created on 2025-06-12
