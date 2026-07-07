import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
-- given
  (a b : α) :
-- imply
  b < -a ↔ a < -b :=
-- proof
  lt_neg


-- created on 2025-03-29
