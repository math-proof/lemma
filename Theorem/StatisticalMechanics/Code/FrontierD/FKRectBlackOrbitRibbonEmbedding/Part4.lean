/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Def.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part4


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

theorem fkRectMedialRibbonBlockCode_embed
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialBlackDart R.medialTorus) (t : Fin 8) :
    (fkRectRibbonCellResidueEmbed R.medialTorus.width
        (fkRectMedialRibbonBlockCode R pairing d t).1,
      fkRectRibbonCellResidueEmbed R.medialTorus.height
        (fkRectMedialRibbonBlockCode R pairing d t).2) =
      fkRectMedialRibbonBlockSite R pairing d t := by
  simp only [fkRectMedialRibbonBlockCode, fkRectMedialRibbonBlockSite]
  let o := fkRectMedialRibbonBlockOffset (pairing d.1.1) d.1.2 t
  change
    (fkRectRibbonCellResidueEmbed R.medialTorus.width
        (fkRectRibbonNormalizeCell R.medialTorus.width_pos d.1.1.1 o.1),
      fkRectRibbonCellResidueEmbed R.medialTorus.height
        (fkRectRibbonNormalizeCell R.medialTorus.height_pos d.1.1.2 o.2)) = _
  rw [fkRectRibbonCellResidueEmbed_normalize,
    fkRectRibbonCellResidueEmbed_normalize]

theorem finitePeriodicSucc_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (finitePeriodicSucc hN) := by
  intro i j h
  simpa only [svCyclicPred_finitePeriodicSucc] using
    congrArg (SixVertexArrows.cyclicPred hN) h

theorem cyclicPred_injective {N : Nat} (hN : 0 < N) :
    Function.Injective (SixVertexArrows.cyclicPred hN) := by
  intro i j h
  simpa only [finitePeriodicSucc_cyclicPred] using
    congrArg (finitePeriodicSucc hN) h

@[simp] theorem finitePeriodicSucc_inj_iff
    {N : Nat} (hN : 0 < N) (i j : Fin N) :
    finitePeriodicSucc hN i = finitePeriodicSucc hN j ↔ i = j :=
  (finitePeriodicSucc_injective hN).eq_iff

@[simp] theorem cyclicPred_inj_iff
    {N : Nat} (hN : 0 < N) (i j : Fin N) :
    SixVertexArrows.cyclicPred hN i =
      SixVertexArrows.cyclicPred hN j ↔ i = j :=
  (cyclicPred_injective hN).eq_iff

set_option maxHeartbeats 2000000 in


theorem fkRectMedialRibbonBlockCode_injective
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus) :
    Function.Injective (fun z :
        FKMedialBlackDart R.medialTorus × Fin 8 =>
      fkRectMedialRibbonBlockCode R pairing z.1 z.2) := by
  rintro ⟨⟨⟨⟨i, j⟩, s⟩, hs⟩, t⟩
    ⟨⟨⟨⟨k, l⟩, q⟩, hq⟩, u⟩ h
  cases hp : pairing (i, j)
  · cases hr : pairing (k, l)
    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all

    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all

  · cases hr : pairing (k, l)
    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all
    · cases s <;> cases q
      all_goals fin_cases t <;> fin_cases u <;>
        simp_all [fkRectMedialRibbonBlockCode,
          fkRectMedialRibbonBlockOffset_eq_table,
          fkRectMedialRibbonBlockOffsetTable,
          fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical] <;>
        try simp_all [fkMedialCheckerColor, fkMedialSideVertical]
      all_goals
        rcases h with ⟨rfl, rfl⟩
        simp [fkMedialCheckerColor, fkMedialSideVertical] at hs hq <;>
          simp_all

theorem fkRectMedialRibbonBlockSite_injective
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus) :
    Function.Injective (fun z :
        FKMedialBlackDart R.medialTorus × Fin 8 =>
      fkRectMedialRibbonBlockSite R pairing z.1 z.2) := by
  intro z w h
  apply fkRectMedialRibbonBlockCode_injective R pairing
  let E := fun c :
      (Fin R.medialTorus.width × Fin 8) ×
        (Fin R.medialTorus.height × Fin 8) =>
    (fkRectRibbonCellResidueEmbed R.medialTorus.width c.1,
      fkRectRibbonCellResidueEmbed R.medialTorus.height c.2)
  have hz : E (fkRectMedialRibbonBlockCode R pairing z.1 z.2) =
      fkRectMedialRibbonBlockSite R pairing z.1 z.2 :=
    fkRectMedialRibbonBlockCode_embed R pairing z.1 z.2
  have hw : E (fkRectMedialRibbonBlockCode R pairing w.1 w.2) =
      fkRectMedialRibbonBlockSite R pairing w.1 w.2 :=
    fkRectMedialRibbonBlockCode_embed R pairing w.1 w.2
  have he : E (fkRectMedialRibbonBlockCode R pairing z.1 z.2) =
      E (fkRectMedialRibbonBlockCode R pairing w.1 w.2) :=
    hz.trans (h.trans hw.symm)
  apply Prod.ext
  · apply fkRectRibbonCellResidueEmbed_injective _
      R.medialTorus.width_pos
    exact congrArg Prod.fst he
  · apply fkRectRibbonCellResidueEmbed_injective _
      R.medialTorus.height_pos
    exact congrArg Prod.snd he


end
end StatMech.FrontierD
