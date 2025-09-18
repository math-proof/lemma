import sympy.functions.elementary.integers
import Lemma.Algebra.Even.is.Any_Eq_Mul2
import Lemma.Algebra.Odd.is.Any_Eq_AddMul2
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n is even ↔ (n + 1) is odd := by
-- proof
  rw [Even.is.Any_Eq_Mul2]
  rw [Odd.is.Any_Eq_AddMul2]
  simp


-- created on 2025-08-13
