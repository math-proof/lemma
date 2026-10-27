import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {x a b : α}
-- given
  (h₀ : x < b)
  (h₁ : x > a) :
-- imply
  x ∈ Ioo a b :=
-- proof
  ⟨h₁, h₀⟩


-- created on 2020-05-07
