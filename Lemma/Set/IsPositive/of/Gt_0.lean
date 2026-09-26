import Lemma.Set.In_Ioi.is.Gt
open Set


@[main]
private lemma main
  [Preorder α] [Zero α]
  {x : α}
-- given
  (h : 0 < x) :
-- imply
  x ∈ Ioi 0 :=
-- proof
  In_Ioi.of.Gt h


-- created on 2026-09-26
