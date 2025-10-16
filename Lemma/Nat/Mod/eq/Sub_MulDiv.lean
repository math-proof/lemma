import Lemma.Nat.Eq_AddMulDiv___Mod
import Lemma.Nat.EqSubS.of.Eq
import Lemma.Nat.EqSubAdd
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n d : Z} :
-- imply
  n % d = n - n / d * d := by
-- proof
  have := Eq_AddMulDiv___Mod (n := n) (d := d)
  have := EqSubS.of.Eq this (n / d * d)
  rw [EqSubAdd.left] at this
  exact this.symm


-- created on 2025-03-16
-- updated on 2025-03-21
