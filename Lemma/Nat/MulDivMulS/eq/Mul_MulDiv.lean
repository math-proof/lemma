import Lemma.Nat.Mul
open Nat


@[main]
private lemma main
-- given
  {z x y : ℕ} :
-- imply
  (z * x) / (z * y) * (z * y) = z * (x / y * y) := by
-- proof
  if hz : z = 0 then
    subst hz
    simp
  else
    calc
      _ = (x * z) / (y * z) * (z * y) := by
        congr 1
        rw [Nat.mul_comm (n := z), Nat.mul_comm (n := z)]
      _ = (x / y) * (z * y) := by rw [Nat.mul_div_mul_right x y (Nat.pos_of_ne_zero hz)]
      _ = z * (x / y * y) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (n := x / y), Nat.mul_assoc]


-- created on 2026-08-03
