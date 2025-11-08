import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {n : ℕ} :
-- imply
  ⌈(n : α)⌉.toNat = n := by
-- proof
  simp


-- created on 2025-05-24
