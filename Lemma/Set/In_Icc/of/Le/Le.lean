import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h₀ : a ≤ x)
  (h₁ : x ≤ b) :
-- imply
  x ∈ Icc a b :=
-- proof
  ⟨h₀, h₁⟩


-- created on 2018-04-07
