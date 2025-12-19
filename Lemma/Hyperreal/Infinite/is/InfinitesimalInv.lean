import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Rat.LtInvS.is.Gt.of.Gt_0.Gt_0
import Lemma.Rat.Ne_0.is.NeInv_0
open Hyperreal Nat Rat


@[main, comm, mp 1, mpr, mp.mt 1, mpr.mt]
private lemma main
  [NeZero (x : ℝ*)] :
-- imply
  Infinite x ↔ Infinitesimal x⁻¹ := by
-- proof
  constructor <;>
    intro h
  ·
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
  ·
    have h_0 := NeZero.ne x
    have : NeZero x⁻¹ := ⟨NeInv_0.of.Ne_0 h_0⟩
    have h := Hyperreal.InfiniteInv.of.Infinitesimal h
    simp at h
    assumption


-- created on 2025-12-10
-- updated on 2025-12-19
