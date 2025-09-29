import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [CancelMonoidWithZero α]
  {d : α}
-- given
  (h : d ≠ 0)
  (x y : α):
-- imply
  d * x = d * y ↔ x = y :=
-- proof
  mul_right_inj' h


@[main, comm, mp, mpr]
private lemma left
  [CancelMonoidWithZero α]
  {d : α}
-- given
  (h : d ≠ 0)
  (x y : α):
-- imply
  x * d = y * d ↔ x = y :=
-- proof
  mul_left_inj' h


-- created on 2025-04-02
