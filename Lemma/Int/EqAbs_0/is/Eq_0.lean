import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [AddGroup α]
  [LinearOrder α]
  [AddLeftMono α]
  [AddRightMono α]
-- given
  (a : α) :
-- imply
  |a| = 0 ↔ a = 0 :=
-- proof
  abs_eq_zero


-- created on 2025-08-02
