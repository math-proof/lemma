import sympy.Basic


@[path]
private lemma main
  [Ring α]
  [LinearOrder α]
  [IsStrictOrderedRing α]
  (a b : α) :
-- imply
  |a| * |b| = |a * b| := by
-- proof
  exact (abs_mul a b).symm


-- created on 2020-02-03
