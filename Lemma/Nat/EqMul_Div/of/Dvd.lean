import Lemma.Nat.EqMulDiv.of.Dvd
import Lemma.Nat.Mul
open Nat


@[path]
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
