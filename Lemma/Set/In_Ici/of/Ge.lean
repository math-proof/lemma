import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {b x : α}
-- given
  (h : b ≤ x) :
-- imply
  x ∈ Ici b :=
-- proof
  h


-- created on 2018-04-06
