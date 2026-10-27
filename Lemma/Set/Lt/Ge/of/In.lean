import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a < x)
  (h₁ : b ≥ x) :
-- imply
  x ∈ Set.Ioc a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2021-05-27
-- updated on 2026-10-26
