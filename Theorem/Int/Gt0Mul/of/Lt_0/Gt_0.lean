module

public import Mathlib
public section


public theorem Int.Gt0Mul.of.Lt_0.Gt_0
  [MulZeroClass α]
  [Preorder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y > 0) :
-- imply
  x * y < 0 :=
-- proof
  mul_neg_of_neg_of_pos h₀ h₁


-- created on 2025-03-23
