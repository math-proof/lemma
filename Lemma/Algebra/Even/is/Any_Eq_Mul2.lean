import sympy.functions.elementary.integers
import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
-- given
  (n : α) :
-- imply
  n is even ↔ ∃ k, n = 2 * k :=
-- proof
  even_iff_exists_two_mul


-- created on 2025-08-13
