import Lemma.Nat.EqSubAdd
import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.SubAdd.eq.Sub_Sub.of.Ge
open Nat


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a ≥ c) :
-- imply
  a + b - (a - c) = b + c := by
-- proof
  rw [Sub_Sub.eq.SubAdd.of.Ge h]
  rw [AddAdd.eq.Add_Add]
  rw [EqSubAdd.left]


@[main]
private lemma comm'
  {a b c : ℕ}
-- given
  (h : a ≥ c) :
-- imply
  a + b - (a - c) = c + b := by
-- proof
  rw [main h]
  rw [Add.comm]


-- created on 2025-11-16
