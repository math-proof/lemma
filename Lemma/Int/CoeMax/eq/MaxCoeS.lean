import sympy.Basic


@[main, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℤ) :
-- imply
  ((a ⊔ b : ℤ) : α) = (a : α) ⊔ (b : α) :=
-- proof
  Int.cast_max


-- created on 2025-10-08
