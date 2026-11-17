module

public import Theorem.Rat.Div.le.Zero.of.Le_0.Gt_0
public import Mathlib

public section

open Rat Nat


public theorem Rat.Div.le.Zero.of.Le_0.Ge_0
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h₀ : x ≤ 0)
  (h₁ : y ≥ 0) :
-- imply
  x / y ≤ 0 := by
-- proof
  obtain hy | hy := Eq.ou.Lt.of.Ge h₁
  ·
    aesop
  ·
    apply Div.le.Zero.of.Le_0.Gt_0 h₀ hy


-- created on 2025-05-05
