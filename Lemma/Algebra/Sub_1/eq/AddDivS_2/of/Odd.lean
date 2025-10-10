import sympy.functions.elementary.integers
import Lemma.Algebra.Mul_2.eq.Add
import Lemma.Algebra.EvenSub_1.of.Odd
import Lemma.Algebra.Eq_AddDivS_2.of.Even
import Lemma.Nat.EqMulS.of.Eq
import Lemma.Algebra.EqDivS_2.of.Odd
open Algebra Nat


@[main, comm]
private lemma main
  [IntegerRing Z]
  {n : Z}
-- given
  (h : n is odd) :
-- imply
  n - 1 = n / 2 + n / 2 := by
-- proof
  have is_even := EvenSub_1.of.Odd h
  rw [Add.eq.Mul_2]
  rw [Eq_AddDivS_2.of.Even is_even]
  rw [Add.eq.Mul_2]
  apply EqMulS.of.Eq
  apply EqDivS_2.of.Odd h


-- created on 2025-08-12
-- updated on 2025-08-13
