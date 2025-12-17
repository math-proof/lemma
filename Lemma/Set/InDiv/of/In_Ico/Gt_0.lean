import Lemma.Set.Ge.of.In_Ico
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Set.Lt.of.In_Ico
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Set.In_Ico.is.Le.Lt
open Set Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : x ∈ Ico a b)
  (h₁ : d > 0) :
-- imply
  x / d ∈ Ico (a / d) (b / d) := by
-- proof
  have h_Ge := Ge.of.In_Ico h₀
  have h_Ge := GeDivS.of.Ge.Gt_0 h_Ge h₁
  have h_Lt := Lt.of.In_Ico h₀
  have h_Lt := LtDivS.of.Lt.Gt_0 h_Lt h₁
  apply In_Ico.of.Le.Lt <;> assumption


-- created on 2025-03-02
