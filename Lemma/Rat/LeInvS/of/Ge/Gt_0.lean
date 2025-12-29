import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Rat.Div.eq.One.of.Gt_0
import Lemma.Nat.Gt.of.Ge.Gt
import Lemma.Rat.LeDivS.of.Le.Gt_0
import Lemma.Rat.DivDiv.eq.Inv.of.Ne_0
import Lemma.Nat.Ne.of.Gt
import Lemma.Rat.Div1.eq.Inv
open Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x a : α}
-- given
  (h₀ : a > 0)
  (h₁ : x ≥ a) :
-- imply
  x⁻¹ ≤ a⁻¹ := by
-- proof
  have := GeDivS.of.Ge.Gt_0 h₁ h₀
  simp [Div.eq.One.of.Gt_0 h₀] at this
  have h_pos := Gt.of.Ge.Gt h₁ h₀
  have := LeDivS.of.Le.Gt_0 this h_pos
  rw [DivDiv.eq.Inv.of.Ne_0 (Ne.of.Gt h_pos)] at this
  rwa [Div1.eq.Inv] at this


-- created on 2025-03-03
-- updated on 2025-03-15
