import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Rat.LtInvS.is.Gt.of.Gt_0.Gt_0
open Hyperreal Nat Rat


@[main]
private lemma main
  {x : ℝ*}
  -- given
  (h₀ : x ≠ 0)
  (h : Infinitesimal x) :
-- imply
  Infinite x⁻¹ := by
-- proof
  apply Infinite.of.All_GtAbs
  have h := All_LtAbs.of.Infinitesimal h
  intro ⟨δ, hδ⟩
  have hδ' := GtInv_0.of.Gt_0 hδ
  have h := h ⟨δ⁻¹, hδ'⟩
  simp at ⊢ h
  apply Gt.of.LtInvS.Gt_0.Gt_0
  repeat simpa


-- created on 2025-12-11
