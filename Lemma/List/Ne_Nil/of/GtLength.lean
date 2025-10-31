import Lemma.List.Ne_Nil.is.GtLength_0
import Lemma.Nat.Gt_0.of.Gt
open List Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h : s.length > i) :
-- imply
  s ≠ [] := by
-- proof
  apply Ne_Nil.of.GtLength_0 ∘ Gt_0.of.Gt
  assumption


-- created on 2025-10-10
