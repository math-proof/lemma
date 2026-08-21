import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]
  {x y : α}
-- given
  (h : |y| = |x|) :
-- imply
  y = x ∨ y = -x :=
-- proof
  abs_eq_abs.mp h


-- created on 2018-08-14
-- updated on 2026-08-20
