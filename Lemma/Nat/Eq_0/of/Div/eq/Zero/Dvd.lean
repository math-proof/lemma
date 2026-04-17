import Lemma.Nat.EqMulDiv.of.Dvd
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h_dvd : b ∣ a)
  (h_zero : a / b = 0) :
-- imply
  a = 0 := by
-- proof
  have key := EqMulDiv.of.Dvd h_dvd
  simp [h_zero] at key
  aesop


-- created on 2026-04-17
