import sympy.Basic


@[main, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℤ) :
-- imply
  ((a ⊓ b : ℤ) : α) = (a : α) ⊓ (b : α) := by
-- proof
  apply Int.cast_min


-- created on 2025-10-08
