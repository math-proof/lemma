import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : b > x) :
-- imply
  x ∈ Set.Ico a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2021-05-20
-- updated on 2026-10-26
