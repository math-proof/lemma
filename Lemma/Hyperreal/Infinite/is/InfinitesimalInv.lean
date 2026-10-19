import Lemma.Hyperreal.Infinitesimal.is.InfiniteInv
import Lemma.Rat.Eq_0.is.EqInv_0
open Hyperreal Nat Rat


@[path, comm, mp 1, mpr, mp.mt 1, mpr.mt]
private lemma main
  [NeZero (x : ℝ*)] :
-- imply
  x → ∞ ↔ x⁻¹ → 0 := by
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
