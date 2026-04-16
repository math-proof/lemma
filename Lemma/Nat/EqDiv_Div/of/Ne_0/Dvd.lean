import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Nat.EqMul_Div.of.Dvd
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {a b : Z}
-- given
  (h_dvd : b ∣ a)
  (h_ne_zero : a ≠ 0) :
-- imply
  a / (a / b) = b := by
-- proof
  have := EqMul_Div.of.Dvd h_dvd
  have := EqDivS.of.Eq this (a / b)
  rw [Mul.comm] at this
  rw [EqDivMul.of.Ne_0.left] at this
  .
    grind
  .
    intro h'
    have hz : a = 0 := by
      have key := EqMul_Div.of.Dvd h_dvd
      rw [h', mul_zero] at key
      exact key.symm
    exact h_ne_zero hz


-- created on 2026-04-16
