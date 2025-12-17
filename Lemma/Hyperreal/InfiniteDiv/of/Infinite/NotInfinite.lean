import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.NotInfinite.is.Any_LeAbs
import Lemma.Nat.Gt.of.Gt.Ge
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.LtMul.is.Lt_Div.of.Gt_0
open Hyperreal Rat Nat


/--
the hypotheses are arranged in the constructor order of division a / b
-/
@[main, mt]
private lemma main
  [NeZero (b : ℝ*)]
  {a : ℝ*}
-- given
  (h_a : Infinite a)
  (h_b : ¬Infinite b) :
-- imply
  Infinite (a / b) := by
-- proof
  have h_b_ne := NeZero.ne b
  apply Infinite.of.All_GtAbs
  intro ⟨δ, hδ⟩
  simp [AbsDiv.eq.DivAbsS]
  let ⟨⟨B, h_B⟩, h_B_le⟩ := Any_LeAbs.of.NotInfinite h_b
  apply Lt_Div.of.LtMul.Gt_0
  ·
    simpa
  ·
    have h_a := All_GtAbs.of.Infinite h_a
    have h_a := h_a ⟨B * δ, by nlinarith⟩
    apply Gt.of.Gt.Ge h_a
    simp_all


-- created on 2025-12-17
