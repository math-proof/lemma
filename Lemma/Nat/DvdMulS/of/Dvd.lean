import Lemma.Nat.Dvd_Mul.of.Dvd
import Lemma.Nat.EqMul_1
open Nat


@[main]
private lemma main
  [CommMonoid α]
-- given
  (h : x ∣ y)
  (a : α) :
-- imply
  x * a ∣ y * a :=
-- proof
  mul_dvd_mul_right h a



@[main]
private lemma left
  [Semigroup α]
-- given
  (h : x ∣ y)
  (a : α) :
-- imply
  a * x ∣ a * y :=
-- proof
  mul_dvd_mul_left a h


-- created on 2025-11-29
