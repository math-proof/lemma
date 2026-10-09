import sympy.functions.elementary.integers
import sympy.Basic


@[path, comm]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n - 1 ≤ n :=
-- proof
  IntegerRing.pred_le n


-- created on 2025-06-02
