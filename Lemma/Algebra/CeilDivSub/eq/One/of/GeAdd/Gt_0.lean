import Lemma.Algebra.Ge_Sub.of.GeAdd
import Lemma.Set.CeilDivSub.eq.One.of.In_Ioc0.Gt_0
import Lemma.Algebra.Sub.gt.Zero.is.Gt
import Lemma.Set.In_Ioc.of.Gt.Le
open Algebra Set


@[main]
private lemma main
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
  have h_Le := Ge_Sub.of.GeAdd.left h₁
  have h_Gt_0 := Sub.gt.Zero.of.Gt h₂
  have h_Mem := In_Ioc.of.Gt.Le h_Gt_0 h_Le
  apply CeilDivSub.eq.One.of.In_Ioc0.Gt_0 h₀ h_Mem


-- created on 2025-05-04
