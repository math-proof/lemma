module

public import Theorem.Set.In_IocDivS.of.In_Ioc.Gt_0
public import Theorem.Rat.EqDiv0_0
public import Theorem.Rat.Div.eq.One.of.Gt_0
public import Theorem.Rat.EqCeil_1.of.In_Ioc0'1

public section

open Set Rat


public theorem Set.CeilDivSub.eq.One.of.In_Ioc0.Gt_0
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {a b : α}
-- given
  (h₀ : b > 0)
  (h₁ : a ∈ Ioc 0 b) :
-- imply
  ⌈a / b⌉ = 1 := by
-- proof
  have := In_IocDivS.of.In_Ioc.Gt_0 h₀ h₁
  simp only [EqDiv0_0] at this
  simp only [Div.eq.One.of.Gt_0 h₀] at this
  apply EqCeil_1.of.In_Ioc0'1 this


-- created on 2025-05-04
