import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Int.Div.ge.FDiv
import Lemma.Int.Div.lt.Add1FDiv
import Lemma.Nat.Add
open Nat Int


@[main, comm]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
-- given
  (n d : ℤ) :
-- imply
  n // d = ⌊n / (d : α)⌋ := by
-- proof
  apply Eq.symm
  rw [EqFloor.is.Le.Lt]
  constructor
  .
    apply Div.ge.FDiv
  .
    rw [Add.comm]
    apply Div.lt.Add1FDiv


-- created on 2025-03-21
-- updated on 2025-03-28
