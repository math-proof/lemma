import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h : x ∈ Icc a b) :
-- imply
  a ≤ x ∧ x ≤ b :=
-- proof
  ⟨h.left, h.right⟩


-- created on 2018-04-05
