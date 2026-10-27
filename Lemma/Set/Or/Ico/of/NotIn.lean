import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a b : ℤ}
-- given
  (h₀ : x ∉ Finset.Ico a b) :
-- imply
  x < a ∨ x ≥ b := by
-- proof
  have h₁ : ¬(a ≤ x ∧ x < b) := by simpa [Finset.mem_Ico] using h₀
  omega


-- created on 2023-06-05
-- updated on 2026-10-26
