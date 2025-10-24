import Lemma.Nat.Mul
import Lemma.Nat.DivMul.eq.Mul_Div.of.Dvd
open Nat


@[main, comm]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h : b ∣ a)
  (c : Z) :
-- imply
  a * c / b = a / b * c := by
-- proof
  rw [Mul.comm]
  rw [Mul.comm (b := c)]
  apply DivMul.eq.Mul_Div.of.Dvd h


-- created on 2025-07-05
-- updated on 2025-10-24
