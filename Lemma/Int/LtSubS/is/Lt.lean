import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LT α]
  [AddRightStrictMono α]
-- given
  (x y c : α) :
-- imply
  x - c < y - c ↔ x < y :=
-- proof
  sub_lt_sub_iff_right c


-- created on 2025-09-30
