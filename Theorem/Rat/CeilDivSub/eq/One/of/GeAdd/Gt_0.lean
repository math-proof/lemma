module

public import Theorem.Int.LeSub.is.Le_Add
public import Theorem.Set.CeilDivSub.eq.One.of.In_Ioc0.Gt_0
public import Theorem.Int.Sub.gt.Zero.is.Gt
public import Theorem.Set.In_Ioc.is.Lt.Le

public section

open Set Int


public theorem Rat.CeilDivSub.eq.One.of.GeAdd.Gt_0
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b c : α}
-- given
  (h₀ : b > 0)
  (h₁ : a + b ≥ c)
  (h₂ : c > a) :
-- imply
  ⌈(c - a) / b⌉ = 1 := by
-- proof
  apply CeilDivSub.eq.One.of.In_Ioc0.Gt_0 h₀
  apply In_Ioc.of.Lt.Le
  .
    apply Sub.gt.Zero.of.Gt h₂
  .
    apply Ge_Sub.of.GeAdd.left h₁


-- created on 2025-05-04
