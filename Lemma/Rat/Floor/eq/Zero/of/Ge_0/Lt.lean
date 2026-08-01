import Lemma.Int.EqFloor.is.Le.Lt
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h₁ : x < 1)
  (h₀ : 0 ≤ x) :
-- imply
  ⌊x⌋ = 0 := by
-- proof
  apply EqFloor.of.Le.Lt (z := 0)
  ·
    simpa using h₀
  ·
    simpa using h₁


-- created on 2018-10-21
