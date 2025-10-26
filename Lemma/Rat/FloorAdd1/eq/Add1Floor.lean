import Lemma.Int.FloorAdd.eq.Add_Floor
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α} :
-- imply
  ⌊1 + x⌋ = 1 +   ⌊x⌋ := by
-- proof
  have := FloorAdd.eq.Add_Floor (x := x) (d := 1)
  norm_cast at this


-- created on 2025-03-25
