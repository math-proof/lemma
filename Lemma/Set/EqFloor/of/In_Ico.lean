import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Set.Le.of.In_Ico
import Lemma.Set.Lt.of.In_Ico
open Set Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {z : ℤ}
  {x : α}
-- given
  (h : x ∈ Ico (z : α) (z + 1)) :
-- imply
  ⌊x⌋ = z := by
-- proof
  apply EqFloor.of.Le.Lt
  ·
    exact Le.of.In_Ico h
  ·
    exact Lt.of.In_Ico h


-- created on 2025-05-04
