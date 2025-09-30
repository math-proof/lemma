import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
-- given
  (x y a : α) :
-- imply
  a - y < a - x ↔ y > x :=
-- proof
  sub_lt_sub_iff_left a


-- created on 2025-09-30
