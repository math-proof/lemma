import Lemma.Basic


@[main, comm]
private lemma int
  [AddGroupWithOne α]
  {a b : ℤ} :
-- imply
  ((a - b : ℤ) : α) = a - b :=
-- proof
  Int.cast_sub a b


@[main, comm]
private lemma main
  [DivisionRing α]
  [CharZero α]
  {a b : ℚ} :
-- imply
  ↑(a - b) = (a - b : α) :=
-- proof
  Rat.cast_sub a b




-- created on 2025-03-28
