import Lemma.Nat.Sub.of.Eq
import Lemma.Nat.EqSubAdd
import Lemma.Int.Eq_AddMulFDiv___FMod
open Nat Int


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n.fmod d = n - n // d * d := by
-- proof
  have := Eq_AddMulFDiv___FMod (n := n) (d := d)
  have := Sub.of.Eq this (n // d * d)
  rw [EqSubAdd.left] at this
  exact this.symm


-- created on 2025-03-21
