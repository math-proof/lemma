import Lemma.Basic


@[main, comm]
private lemma nat
  [LinearOrderedSemiring  α]
-- given
  (a b : ℕ) :
-- imply
  ((a ⊓ b : ℕ) : α) = (a: α) ⊓ (b :α) :=
-- proof
  Nat.cast_min a b


@[main, comm]
private lemma int
  [LinearOrderedRing α]
-- given
  (a b : ℤ) :
-- imply
  ((a ⊓ b : ℤ) : α) = (a: α) ⊓ (b :α) :=
-- proof
  Int.cast_min


@[main, comm]
private lemma rat
  [LinearOrderedField α]
-- given
  (a b : ℚ) :
-- imply
  ((a ⊓ b : ℚ) : α) = (a: α) ⊓ (b :α) :=
-- proof
  Rat.cast_min a b

-- created on 2025-08-04
