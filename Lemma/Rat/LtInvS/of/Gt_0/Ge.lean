import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Algebra.DivDiv.eq.Inv.of.Ne_0
import Lemma.Nat.Ne.of.Gt
import Lemma.Algebra.Div1.eq.Inv
import Lemma.Rat.GtDivS.of.Gt.Gt_0
import Lemma.Algebra.Gt.of.Gt.Gt
import Lemma.Rat.LtDivS.of.Lt.Gt_0
open Algebra Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a : α}
-- given
  (h₀ : a > 0)
  (h₁ : x > a) :
-- imply
  x⁻¹ < a⁻¹ := by
-- proof
  have := GtDivS.of.Gt.Gt_0 h₁ h₀
  simp [Div.eq.One.of.Gt_0 h₀] at this
  have h_Gt_0 := Gt.of.Gt.Gt h₁ h₀
  have := LtDivS.of.Lt.Gt_0 this h_Gt_0
  rw [DivDiv.eq.Inv.of.Ne_0 (Ne.of.Gt h_Gt_0)] at this
  rwa [Div1.eq.Inv] at this


-- created on 2025-03-15
