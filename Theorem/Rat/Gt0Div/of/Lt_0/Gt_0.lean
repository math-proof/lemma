module

public import Theorem.Rat.GtInv_0.is.Gt_0
public import Theorem.Int.Gt0Mul.of.Lt_0.Gt_0
public import Theorem.Rat.Div.eq.Mul_Inv

public section

open Int Rat


public theorem Rat.Gt0Div.of.Lt_0.Gt_0
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y > 0) :
-- imply
  x / y < 0 := by
-- proof
  have h₁ := GtInv_0.of.Gt_0 h₁
  have := Gt0Mul.of.Lt_0.Gt_0 h₀ h₁
  rwa [Mul_Inv.eq.Div] at this


-- created on 2025-03-30
