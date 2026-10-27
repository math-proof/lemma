import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [PartialOrder α]
  {a b x : α}
-- given
  (h₀ : b ≤ x)
  (h₁ : x ∈ Icc a b) :
-- imply
  x = b :=
-- proof
  le_antisymm h₁.right h₀


-- created on 2020-05-07
