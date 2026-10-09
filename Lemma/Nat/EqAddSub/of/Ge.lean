import sympy.functions.elementary.integers
import sympy.Basic


@[path]
private lemma main
  [IntegerRing N]
  {a b : N}
-- given
  (h : b ≥ a) :
-- imply
  b - a + a = b :=
-- proof
  IntegerRing.sub_add_cancel h


-- created on 2025-03-15
-- updated on 2025-06-08
