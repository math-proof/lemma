import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b d x : ℤ}
-- given
  (h₀ : 0 < d)
  (h₁ : a ≤ x)
  (h₂ : x < b)
  (h₃ : ∃ k : ℕ, x = a + (k : ℤ) * d) :
-- imply
  0 < d ∧ a ≤ x ∧ x < b ∧ x % d = a % d := by
-- proof
  refine ⟨h₀, h₁, h₂, ?_⟩
  obtain ⟨k, hk⟩ := h₃
  rw [hk]
  exact Int.add_mul_emod_self_right a (k : ℤ) d


-- created on 2022-01-01
-- updated on 2026-10-26
