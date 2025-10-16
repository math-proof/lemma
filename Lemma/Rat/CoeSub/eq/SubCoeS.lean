import sympy.Basic


@[main, comm]
private lemma main
  [DivisionRing α]
  [CharZero α]
  {a b : ℚ} :
-- imply
  ↑(a - b) = (a - b : α) :=
-- proof
  Rat.cast_sub a b


-- created on 2025-10-16
