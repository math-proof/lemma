import sympy.Basic


@[main, comm]
private lemma nat
  [AddMonoidWithOne α]
-- given
  (a b : ℕ) :
-- imply
  ((a + b : ℕ) : α) = a + b :=
-- proof
  Nat.cast_add a b


@[main, comm]
private lemma int
  [AddGroupWithOne α]
-- given
  (a b : ℤ) :
-- imply
  ((a + b : ℤ) : α) = a + b :=
-- proof
  Int.cast_add a b


@[main, comm]
private lemma main
  [DivisionRing α]
  [CharZero α]
-- given
  (a b : ℚ) :
-- imply
  ↑(a + b) = (a + b : α) :=
-- proof
  Rat.cast_add a b


-- created on 2025-03-25
