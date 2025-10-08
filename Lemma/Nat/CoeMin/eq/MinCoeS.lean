import sympy.Basic


@[main, comm]
private lemma main
  [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℕ) :
-- imply
  ((a ⊓ b : ℕ) : α) = (a : α) ⊓ (b : α) :=
-- proof
  Nat.cast_min a b


-- created on 2025-10-08
