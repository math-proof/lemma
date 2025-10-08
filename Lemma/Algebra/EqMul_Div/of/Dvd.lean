import Lemma.Algebra.EqMulDiv.of.Dvd
import Lemma.Nat.Mul
open Algebra Nat


@[main]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : a ∣ b) :
-- imply
  a * (b / a) = b := by
-- proof
  rw [Mul.comm]
  apply EqMulDiv.of.Dvd h


-- created on 2025-07-12
