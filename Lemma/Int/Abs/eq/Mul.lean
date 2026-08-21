import sympy.Basic


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  |a * b| = |a| * |b| :=
-- proof
  abs_mul a b


-- created on 2018-02-12
-- updated on 2026-08-20
