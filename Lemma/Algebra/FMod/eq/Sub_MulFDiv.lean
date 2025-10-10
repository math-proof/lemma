import Lemma.Algebra.EqSubS.of.Eq
import Lemma.Nat.EqSubAdd
import Lemma.Algebra.Eq_AddMulFDiv___FMod
open Algebra Nat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n.fmod d = n - n // d * d := by
-- proof
  have := Eq_AddMulFDiv___FMod (n := n) (d := d)
  have := EqSubS.of.Eq.int this (n // d * d)
  rw [EqSubAdd.left] at this
  exact this.symm


-- created on 2025-03-21
