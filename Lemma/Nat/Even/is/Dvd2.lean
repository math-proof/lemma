import sympy.functions.elementary.integers
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
-- given
  (n : α) :
-- imply
  n is even ↔ 2 ∣ n :=
-- proof
  even_iff_two_dvd


-- created on 2025-08-12
