import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.Div.ge.Zero
import Lemma.Rat.LtDiv.of.Lt_Mul.Gt_0
open Rat Int


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {n k : ℕ}
-- given
  (h : k < n) :
-- imply
  ⌊(k : α) / n⌋ = 0 := by
-- proof
  apply EqFloor.of.Le.Lt
  ·
    simp [Div.ge.Zero]
  ·
    simp
    apply LtDiv.of.Lt_Mul.Gt_0
    ·
      simpa
    ·
      simp
      linarith


-- created on 2025-07-07
