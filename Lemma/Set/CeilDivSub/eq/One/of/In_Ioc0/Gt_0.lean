import sympy.sets.sets
import Lemma.Set.In_IocDivS.of.In_Ioc.Gt_0
import Lemma.Algebra.EqDiv0'0
import Lemma.Rat.Div.eq.One.of.Gt_0
import Lemma.Rat.EqCeil_1.of.In_Ioc0'1
open Set Algebra Rat


@[main]
private lemma main
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
  simp only [EqDiv0'0] at this
  simp only [Div.eq.One.of.Gt_0 h₀] at this
  apply EqCeil_1.of.In_Ioc0'1 this


-- created on 2025-05-04
