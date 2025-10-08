import sympy.Basic


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
-- updated on 2025-10-08
