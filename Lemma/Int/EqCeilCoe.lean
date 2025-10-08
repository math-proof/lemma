import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
-- given
  (a : ℤ) :
-- imply
  ⌈(a : α)⌉ = a := by
-- proof
  aesop


-- created on 2025-08-04
-- updated on 2025-10-08
