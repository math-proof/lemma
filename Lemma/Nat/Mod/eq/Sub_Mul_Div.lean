import Lemma.Nat.EqAddMul_Div
import Lemma.Nat.EqSubAdd
import Lemma.Nat.EqSubS.of.Eq
open Nat


@[main]
private lemma main
  [IntegerRing Z]
  {n d : Z} :
-- imply
  n % d = n - d * (n / d) := by
-- proof
  have := EqAddMul_Div (n := n) (d := d)
  have := EqSubS.of.Eq this (d * (n / d))
  rwa [EqSubAdd.left] at this


-- created on 2026-07-12
