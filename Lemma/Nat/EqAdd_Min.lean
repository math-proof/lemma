import Lemma.Nat.Add
import Lemma.Nat.EqAddMin
import Lemma.Nat.Min
open Nat


@[main]
private lemma main
-- given
  (a b : ℕ) :
-- imply
  a - b + a ⊓ b = a := by
-- proof
  rw [Add.comm]
  apply EqAddMin


@[main]
private lemma comm'
-- given
  (a b : ℕ) :
-- imply
  a - b + b ⊓ a = a := by
-- proof
  rw [Min.comm]
  apply main


-- created on 2025-10-27
