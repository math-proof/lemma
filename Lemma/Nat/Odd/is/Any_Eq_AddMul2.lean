import sympy.functions.elementary.integers
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Semiring α]
-- given
  (n : α) :
-- imply
  n is odd ↔ ∃ k, n = 2 * k + 1 :=
-- proof
  odd_iff_exists_bit1


-- created on 2025-03-04
-- updated on 2025-08-13
