import Lemma.Rat.FloorDiv.eq.Zero.of.Lt
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.Div.ge.Zero
import Lemma.Rat.LtDiv.is.Lt_Mul.of.Gt_0
import Lemma.Nat.Gt_0
open Nat Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {n : ℕ}
-- given
  (j : Fin n) :
-- imply
  ⌊((j : ℕ) : α) / n⌋ = 0 := by
-- proof
  apply Rat.FloorDiv.eq.Zero.of.Lt
  simp


-- created on 2025-07-06
