import sympy.Basic


@[main, comm]
private lemma nat
  [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℕ) :
-- imply
  ((a ⊔ b : ℕ) : α) = (a : α) ⊔ (b : α) :=
-- proof
  Nat.cast_max a b


@[main, comm]
private lemma int
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℤ) :
-- imply
  ((a ⊔ b : ℤ) : α) = (a : α) ⊔ (b : α) :=
-- proof
  Int.cast_max


@[main, comm]
private lemma rat
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : ℚ) :
-- imply
  ((a ⊔ b : ℚ) : α) = (a : α) ⊔ (b : α) :=
-- proof
  Rat.cast_max a b


-- created on 2025-08-04
