import Lemma.Hyperreal.Infinite.is.All_GtAbs
import Lemma.Hyperreal.Infinitesimal.is.All_LtAbs
import Lemma.Nat.Gt.of.Gt.Gt
import Lemma.Rat.GtInv_0.is.Gt_0
import Lemma.Rat.LtInvS.is.Gt.of.Gt_0.Gt_0
open Hyperreal Nat Rat


/--
| attributes | lemma |
| :---: | :---: |
| main | Hyperreal.Infinitesimal.is.InfiniteInv |
| comm | Hyperreal.InfiniteInv.is.Infinitesimal |
| mp   | Hyperreal.InfiniteInv.of.Infinitesimal |
| mpr 1| Hyperreal.Infinitesimal.of.InfiniteInv |
| mp.mt | Hyperreal.NotInfinitesimal.of.NotInfiniteInv |
| mpr.mt 1| Hyperreal.NotInfiniteInv.of.NotInfinitesimal |
-/
@[main, comm, mp, mpr 1, mp.mt, mpr.mt 1]
private lemma main
  [NeZero (x : ℝ*)] :
-- imply
  Infinitesimal x ↔ Infinite x⁻¹ := by
-- proof
  constructor <;>
    intro h
  .
    rw [Infinitesimal.is.All_LtAbs] at h
    rw [Infinite.is.All_GtAbs]
    intro ⟨δ, hδ⟩
    have hδ' := GtInv_0.of.Gt_0 hδ
    have h := h ⟨δ⁻¹, hδ'⟩
    simp at ⊢ h
    apply Gt.of.LtInvS.Gt_0.Gt_0
    .
      have := NeZero.ne x
      simpa
    .
      simpa
    .
      simpa
  .
    rw [Infinite.is.All_GtAbs] at h
    rw [Infinitesimal.is.All_LtAbs]
    intro ⟨δ, hδ⟩
    have hδ' := GtInv_0.of.Gt_0 hδ
    have h := h ⟨δ⁻¹, hδ'⟩
    simp at ⊢ h
    apply Gt.of.LtInvS.Gt_0.Gt_0
    .
      simpa
    .
      apply Gt_0.of.GtInv_0
      apply Gt.of.Gt.Gt h
      simpa
    .
      simpa


 -- created on 2025-12-11
