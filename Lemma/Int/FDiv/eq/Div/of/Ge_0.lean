import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d ≥ 0) :
-- imply
  n // d = n / d :=
-- proof
  Int.fdiv_eq_ediv_of_nonneg n h


-- created on 2025-03-21
