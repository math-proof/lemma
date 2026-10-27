import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x a b : ℝ}
-- given
  (h₀ : x ≤ b)
  (h₁ : x > a) :
-- imply
  x ∈ Set.Ioc a b := by
-- proof
  exact ⟨h₁, h₀⟩


-- created on 2021-05-20
