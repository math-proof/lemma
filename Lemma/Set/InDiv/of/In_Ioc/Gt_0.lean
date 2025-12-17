import Lemma.Set.Gt.of.In_Ioc
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Set.Le.of.In_Ioc
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Set.In_Ioc.is.Lt.Le
open Set Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioc a b)
  (h₁ : d > 0) :
-- imply
  x / d ∈ Ioc (a / d) (b / d) := by
-- proof
  have h_Gt := Gt.of.In_Ioc h₀
  have h_Gt := GtDivS.of.Gt.Gt_0 h_Gt h₁
  have h_Le := Le.of.In_Ioc h₀
  have h_Ge := LeDivS.of.Le.Gt_0 h_Le h₁
  apply In_Ioc.of.Lt.Le <;> assumption


-- created on 2025-03-01
-- updated on 2025-03-02
