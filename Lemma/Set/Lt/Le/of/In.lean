import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : x < a)
  (h₁ : b ≤ x) :
-- imply
  x ∈ Set.Ico b a :=
-- proof
  ⟨h₁, h₀⟩


-- created on 2021-05-30
-- updated on 2026-10-26
