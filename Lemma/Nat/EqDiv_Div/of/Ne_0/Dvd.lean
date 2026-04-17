import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.EqDivS.of.Eq
import Lemma.Nat.EqMul_Div.of.Dvd
import Lemma.Nat.Eq_0.of.Div.eq.Zero.Dvd
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
    have := Eq_0.of.Div.eq.Zero.Dvd h_dvd h'
    contradiction


-- created on 2026-04-16
