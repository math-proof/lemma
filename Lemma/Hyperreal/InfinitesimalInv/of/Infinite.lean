import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Rat.LtInvS.is.Gt.of.Gt_0.Gt_0
open Hyperreal Rat Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : Infinite x) :
-- imply
  Infinitesimal x⁻¹ := by
-- proof
  apply Infinitesimal.of.All_LtAbs
  have h := All_GtAbs.of.Infinite h
  intro ⟨δ, hδ⟩
  have hδ' := GtInv_0.of.Gt_0 hδ
  have h := h ⟨δ⁻¹, hδ'⟩
  simp at ⊢ h
  apply Gt.of.LtInvS.Gt_0.Gt_0
  ·
    simpa
  ·
    apply GtInv_0.of.Gt_0
    apply Gt.of.Gt.Gt h
    simpa
  ·
    simpa


-- created on 2025-12-10
-- updated on 2025-12-11
