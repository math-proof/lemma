import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.EqMul_1
open Nat


@[main]
private lemma main
  [CommMonoid α]
-- given
  (x a : α) :
-- imply
  a ∣ x * a := by
-- proof
  apply Dvd_Mul.of.Dvd
  use 1
  rw [EqMul_1]


@[main]
private lemma left
  [Monoid α]
-- given
  (a x : α) :
-- imply
  a ∣ a * x := by
-- proof
  apply Dvd_Mul.of.Dvd.left
  use 1
  rw [EqMul_1]


-- created on 2025-07-09
