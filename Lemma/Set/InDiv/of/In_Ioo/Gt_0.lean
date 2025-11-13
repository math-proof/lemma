import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Set.Gt.of.In_Ioo
import Lemma.Rat.LtDivS.of.Lt.Gt_0
import Lemma.Set.Lt.of.In_Ioo
import Lemma.Set.In_Ioo.of.Lt.Lt
open Set Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h₀ : x ∈ Ioo a b)
  (h₁ : d > 0) :
-- imply
  x / d ∈ Ioo (a / d) (b / d) := by
-- proof
  have h_Gt := Gt.of.In_Ioo h₀
  have h_Gt := GtDivS.of.Gt.Gt_0 h_Gt h₁
  have h_Lt := Lt.of.In_Ioo h₀
  have h_Lt := LtDivS.of.Lt.Gt_0 h_Lt h₁
  apply In_Ioo.of.Lt.Lt <;> assumption


-- created on 2025-03-02
