import Lemma.Hyperreal.Any_Ge.of.NotInfinitesimal
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Nat.Gt.of.Ge.Gt
import Lemma.Nat.LeMulS.of.Le.Gt_0
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.LtDiv.is.Lt_Mul.of.Gt_0
open Hyperreal Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  Infinitesimal (a / b) := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  intro ⟨δ, hδ⟩
  simp [AbsDiv.eq.DivAbsS]
  let ⟨⟨B, h_B⟩, h_B_le⟩ := Any_Ge.of.NotInfinitesimal h_b
  apply LtDiv.of.Lt_Mul.Gt_0
  ·
    apply Gt.of.Ge.Gt h_B_le
    simpa
  ·
    have h_a := All_LtAbs.of.Infinitesimal h_a
    calc _ < _ := h_a ⟨B * δ, by nlinarith⟩
      _ ≤ _ := LeMulS.of.Le.Gt_0 h_B_le (by simpa)


-- created on 2025-12-09
