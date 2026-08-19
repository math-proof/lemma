import Lemma.Set.Lt.of.Ico.ne.Empty
import Lemma.Nat.NotLt.of.Ge
open Set Nat


@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x ≥ y) :
-- imply
  Ico x y = ∅ := by
-- proof
  by_contra h_ne
  have := Lt.of.Ico.ne.Empty h_ne
  have := NotLt.of.Ge h
  contradiction


-- created on 2021-06-15
