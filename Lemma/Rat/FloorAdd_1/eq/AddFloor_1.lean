import Lemma.Int.FloorAdd.eq.AddFloor
open Int


@[main]
private lemma main
  [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
  [FloorRing R]
  {x : R} :
-- imply
  ⌊x + 1⌋ =   ⌊x⌋ + 1 := by
-- proof
  have := FloorAdd.eq.AddFloor (x := x) (d := 1)
  norm_cast at this


-- created on 2025-03-25
