import sympy.functions.elementary.integers
import Lemma.Nat.Mul_2.eq.Add
import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Nat.Even.is.Dvd2
open Nat


@[main, comm]
private lemma main
  [IntegerRing α]
  {n : α}
-- given
  (h : n is even) :
-- imply
  n = n / 2 + n / 2 := by
-- proof
  rw [Add.eq.Mul_2]
  rw [EqMulDiv.of.Dvd]
  apply Dvd2.of.Even
  assumption


-- created on 2025-08-12
