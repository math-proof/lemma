import Lemma.Int.CeilAdd.eq.Add_Ceil
import Lemma.Int.CeilNeg.eq.NegFloor
import Lemma.Int.Sub.eq.Add_Neg
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  -- given
  (d : ℤ)
  (x : α) :
-- imply
  ⌈d - x⌉ = d - ⌊x⌋ := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [CeilAdd.eq.Add_Ceil]
  rw [CeilNeg.eq.NegFloor]
  rw [Add_Neg.eq.Sub]


-- created on 2025-11-07
