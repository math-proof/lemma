module

public import Theorem.Nat.Le.is.Lt.ou.Eq
public import Theorem.Nat.Le.of.Lt
public import Theorem.Rat.Gt0Div.of.Lt_0.Gt_0

public section

open Nat Rat


public theorem Rat.Div.le.Zero.of.Le_0.Gt_0
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y > 0) :
-- imply
  x / y ≤ 0 := by
-- proof
  obtain hx | hx := Lt.ou.Eq.of.Le h₀
  ·
    apply Le.of.Lt
    apply Gt0Div.of.Lt_0.Gt_0 hx h₁
  ·
    simp_all


-- created on 2025-05-05
