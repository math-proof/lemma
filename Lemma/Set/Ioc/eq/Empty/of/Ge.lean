import Lemma.Set.Lt.of.Ioc.ne.Empty
import Lemma.Nat.NotLt.of.Ge
open Set Nat


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  Ioc x y = ∅ := by
-- proof
  by_contra h_ne
  have := Lt.of.Ioc.ne.Empty h_ne
  have := NotLt.of.Ge h
  contradiction


-- created on 2018-10-17
