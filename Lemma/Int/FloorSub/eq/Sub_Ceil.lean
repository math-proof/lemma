import Lemma.Int.FloorAdd.eq.Add_Floor
import Lemma.Int.FloorNeg.eq.NegCeil
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
  ⌊d - x⌋ = d - ⌈x⌉ := by
-- proof
  rw [Sub.eq.Add_Neg]
  rw [FloorAdd.eq.Add_Floor]
  rw [FloorNeg.eq.NegCeil]
  rw [Add_Neg.eq.Sub]


-- created on 2025-11-07
