import Lemma.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}:
-- imply
  ⌈x - 1⌉ = ⌈x⌉ - 1 := by
-- proof
  simp


-- created on 2025-05-04
