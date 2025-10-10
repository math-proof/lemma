import Lemma.Nat.EqSubAdd
import Lemma.Nat.Add
import Lemma.Algebra.Sub_Add.eq.SubSub
open Algebra Nat


@[main, comm]
private lemma main
  {b c : ℕ}
-- given
  (h : b ≥ c)
  (a : ℕ) :
-- imply
  a + c - b = a - (b - c) := by
-- proof
  let d := b - c
  have h_b : b = d + c := by
    simp [d, h]
  rw [h_b]
  rw [EqSubAdd]
  rw [Add.comm (a := d)]
  rw [Sub_Add.eq.SubSub.nat]
  rw [EqSubAdd]


-- created on 2025-06-20
