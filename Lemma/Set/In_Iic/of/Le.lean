import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {b n : α}
-- given
  (h : n ≤ b) :
-- imply
  n ∈ Iic b :=
-- proof
  h


-- created on 2019-11-16
