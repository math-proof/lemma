import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (a : ℕ) :
-- imply
  ⌈(a : α)⌉ = a := by
-- proof
  aesop


-- created on 2025-10-08
