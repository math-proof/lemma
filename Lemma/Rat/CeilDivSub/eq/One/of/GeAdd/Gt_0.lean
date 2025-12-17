import Lemma.Int.LeSub.is.Le_Add
import Lemma.Set.CeilDivSub.eq.One.of.In_Ioc0.Gt_0
import Lemma.Int.Sub.gt.Zero.is.Gt
import Lemma.Set.In_Ioc.is.Lt.Le
open Set Int


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
  apply CeilDivSub.eq.One.of.In_Ioc0.Gt_0 h₀
  apply In_Ioc.of.Lt.Le h_Gt_0 h_Le


-- created on 2025-05-04
