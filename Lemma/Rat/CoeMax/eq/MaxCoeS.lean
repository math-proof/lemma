import sympy.Basic


@[main, comm]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℚ) :
-- imply
  ((a ⊔ b : ℚ) : α) = (a : α) ⊔ (b : α) :=
-- proof
  Rat.cast_max a b


-- created on 2025-10-08
