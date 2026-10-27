import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x ≤ b)
  (h₁ : a ≤ x) :
-- imply
  x ∈ Set.Icc a b := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2021-05-23
