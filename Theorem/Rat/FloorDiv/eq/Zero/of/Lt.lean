module

public import Theorem.Int.EqFloor.is.Le.Lt
public import Theorem.Rat.Div.ge.Zero
public import Theorem.Rat.LtDiv.is.Lt_Mul.of.Gt_0

public section

open Rat Int


public theorem Rat.FloorDiv.eq.Zero.of.Lt
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
      simp
      linarith
    ·
      simpa


-- created on 2025-07-07
