import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Preorder α]
  {b x : α}
-- given
  (h : x < b) :
-- imply
  x ∈ Iio b :=
-- proof
  h


-- created on 2018-04-06
