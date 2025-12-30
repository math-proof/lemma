import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LT α]
  [AddRightStrictMono α]
  {a b : α} :
-- imply
  a - b < 0 ↔ a < b :=
-- proof
  sub_neg


-- created on 2025-12-30
