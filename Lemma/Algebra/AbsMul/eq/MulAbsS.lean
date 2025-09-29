import sympy.Basic


@[main, comm]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a b : α) :
-- imply
  |a * b| = |a| * |b| :=
  -- proof
  abs_mul a b


-- created on 2025-04-19
