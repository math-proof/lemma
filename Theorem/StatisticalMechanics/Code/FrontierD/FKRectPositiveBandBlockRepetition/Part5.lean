/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierLocalizedCycle
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierForceTopology
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierPattern
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDualSourceBarrierRate
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
import Def.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition.Part5
open Set SimpleGraph Filter Topology


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    IsIncreasing (fkRectPositiveBandBlockBottomConnectorEvent B hheight) :=
  fkRectConnectedWithin_isIncreasing R _ _ _

theorem fkRectPositiveBandBlockTopConnectorEvent_isIncreasing
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1) :
    IsIncreasing (fkRectPositiveBandBlockTopConnectorEvent B hheight) :=
  fkRectConnectedWithin_isIncreasing R _ _ _


theorem fkRectCritical_cFE_pow_le_bottomConnector
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hproper : 4 * scale + 1 < R.width)
    (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ^
        ((4 * scale + 1) * (24 * scale + 4)) ≤
      fkRectCriticalEventMass R q
        (fkRectPositiveBandBlockBottomConnectorEvent B hheight) := by
  let S0 := fkRectColumnBand R 1 (4 * scale + 1) 1 (24 * scale + 4)
  let x0 : FKRectInducedVertex R S0 :=
    ⟨fkRectRowOneVertex R (fkRectUnitGapColumn R), by
      change 1 ≤ 1 ∧ 1 ≤ 4 * scale + 1 ∧
        1 ≤ 1 ∧ 1 ≤ 24 * scale + 4
      omega⟩
  let y0 : FKRectInducedVertex R S0 :=
    ⟨B.start.1, by
      exact ⟨(B.column_bound B.start.1 B.start.2).1,
        (B.column_bound B.start.1 B.start.2).2,
        (B.row_bound B.start.1 B.start.2).1,
        (B.row_bound B.start.1 B.start.2).2⟩⟩
  have hbase := fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass
    R (4 * scale + 1) 1 (24 * scale + 4)
      (by omega) hproper (by omega) (by omega) hq x0 y0
  have hsubset :
      {omega | FKRectConnectedWithin R omega S0 x0 y0} ⊆
        fkRectPositiveBandBlockBottomConnectorEvent B hheight := by
    intro omega homega
    have hmono := homega.mono_set R omega (T :=
        fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) (by
      intro v hv
      exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.trans hheight⟩)
    unfold fkRectPositiveBandBlockBottomConnectorEvent
    change FKRectConnectedWithin R omega
      (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) _ _
    convert hmono using 1
    · apply Subtype.ext
      rw [fkRectPositiveBandBlockPathVertex_val]
      simpa [y0] using
        (fkRectEvenRowTranslationVertexEquiv_zero R B.start.1)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmonoMass := fkRectCriticalEventMass_mono R hq0 hsubset
  simpa [S0] using hbase.trans hmonoMass

theorem fkRectPositiveBandBlockPathVertex_last_row_lower
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale) :
    R.height - 1 - (40 * scale + 6) ≤
      (fkRectPositiveBandBlockPathVertex B hheight
        (Fin.last (fkRectPositiveBandBulkBlocks B))).1.2.val := by
  have hmul := fkRectPositiveBandBulkBlocks_mul_step_le B
  have hrow := B.row_bound B.start.1 B.start.2
  have hrecover :
      R.height - 1 - (24 * scale + 4) + (24 * scale + 4) =
        R.height - 1 := Nat.sub_add_cancel hheight
  have hrem := fkRectPositiveBandBulkBlocks_remainder_lt B hscale
  have hlt : B.start.1.2.val +
      fkRectPositiveBandBulkBlocks B * B.step < R.height := by omega
  rw [fkRectPositiveBandBlockPathVertex_val,
    fkRectEvenRowTranslationVertexEquiv_apply]
  change R.height - 1 - (40 * scale + 6) ≤
    (fkRectRowTranslate R
      (((Fin.last (fkRectPositiveBandBulkBlocks B)).val : Nat) * B.step)
      B.start.1.2).val
  rw [show (Fin.last (fkRectPositiveBandBulkBlocks B)).val =
      fkRectPositiveBandBulkBlocks B by rfl]
  rw [show fkRectRowTranslate R
      ((fkRectPositiveBandBulkBlocks B : Int) * (B.step : Int))
        B.start.1.2 =
      ⟨B.start.1.2.val +
        fkRectPositiveBandBulkBlocks B * B.step, hlt⟩ by
      simpa [Nat.cast_mul] using
        (fkRectRowTranslate_eq_add_of_lt R
          (fkRectPositiveBandBulkBlocks B * B.step) B.start.1.2 hlt)]
  simp only [Fin.val_mk]
  have hstep := B.step_upper
  omega


theorem fkRectCritical_cFE_pow_le_topConnector
    {R : FKRectTorus} {q : Real} {scale : Nat}
    (B : FKRectPositiveBandOrientedBlock R q scale)
    (hheight : 24 * scale + 4 ≤ R.height - 1)
    (hscale : 3 ≤ scale)
    (htall : 40 * scale + 6 < R.height - 1)
    (hproper : 4 * scale + 1 < R.width)
    (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ^
        ((4 * scale + 1) * (40 * scale + 7)) ≤
      fkRectCriticalEventMass R q
        (fkRectPositiveBandBlockTopConnectorEvent B hheight) := by
  let lower := R.height - 1 - (40 * scale + 6)
  let S1 := fkRectColumnBand R 1 (4 * scale + 1) lower (R.height - 1)
  have hlower : 1 ≤ lower := by dsimp [lower]; omega
  have hlowerLast : lower < R.height - 1 := by dsimp [lower]; omega
  let x1 : FKRectInducedVertex R S1 :=
    ⟨(fkRectPositiveBandBlockPathVertex B hheight
      (Fin.last (fkRectPositiveBandBulkBlocks B))).1, by
        have hv := (fkRectPositiveBandBlockPathVertex B hheight
          (Fin.last (fkRectPositiveBandBulkBlocks B))).2
        exact ⟨hv.1, hv.2.1,
          fkRectPositiveBandBlockPathVertex_last_row_lower
            B hheight hscale, hv.2.2.2⟩⟩
  let y1 : FKRectInducedVertex R S1 :=
    ⟨fkRectLastRowVertex R (fkRectUnitGapColumn R), by
      change 1 ≤ 1 ∧ 1 ≤ 4 * scale + 1 ∧
        lower ≤ (svFinLast R.height_pos).val ∧
          (svFinLast R.height_pos).val ≤ R.height - 1
      exact ⟨by omega, by omega, by simp [svFinLast]; omega,
        by simp [svFinLast]⟩⟩
  have hbase := fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass
    R (4 * scale + 1) lower (R.height - 1)
      (by omega) hproper hlowerLast (by omega) hq x1 y1
  have hsubset :
      {omega | FKRectConnectedWithin R omega S1 x1 y1} ⊆
        fkRectPositiveBandBlockTopConnectorEvent B hheight := by
    intro omega homega
    have hmono := homega.mono_set R omega (T :=
        fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) (by
      intro v hv
      exact ⟨hv.1, hv.2.1, hlower.trans hv.2.2.1, hv.2.2.2⟩)
    unfold fkRectPositiveBandBlockTopConnectorEvent
    change FKRectConnectedWithin R omega
      (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) _ _
    exact hmono
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmonoMass := fkRectCriticalEventMass_mono R hq0 hsubset
  have hheightCount : R.height - 1 + 1 - lower = 40 * scale + 7 := by
    dsimp [lower]
    omega
  simpa [S1, hheightCount] using hbase.trans hmonoMass

theorem fkRectUnitAttachmentOpenEvent_isIncreasing
    (R : FKRectTorus) :
    IsIncreasing (fkRectUnitAttachmentOpenEvent R) := by
  intro omega tau hot homega
  change omega (fkRectRowZeroAttachmentEdgeAt R
    (fkRectUnitGapColumn R)) = true at homega
  change tau (fkRectRowZeroAttachmentEdgeAt R
    (fkRectUnitGapColumn R)) = true
  cases htau : tau (fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R))
  · have hle := hot (fkRectRowZeroAttachmentEdgeAt R
        (fkRectUnitGapColumn R))
    rw [homega, htau] at hle
    exact ((by decide : ¬ (true ≤ false)) hle).elim
  · rfl

theorem fkRectCriticalOpenMass_singleton_eq_eventMass
    (R : FKRectTorus) (q : Real) (a : R.EdgeIndex) :
    fkRectCriticalOpenMass R q {a} =
      fkRectCriticalEventMass R q {omega | omega a = true} := by
  classical
  unfold fkRectCriticalOpenMass fkRectCriticalEventMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases h : omega a = true
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

theorem fkRectCritical_cFE_le_unitAttachmentOpenEvent
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) :
    FK.cFE (fkRectCriticalP q) q ≤
      fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) := by
  have h := fkRectCritical_cFE_pow_le_openMass R hq
    ({fkRectRowZeroAttachmentEdgeAt R
      (fkRectUnitGapColumn R)} : Finset R.EdgeIndex)
  rw [Finset.card_singleton, pow_one,
    fkRectCriticalOpenMass_singleton_eq_eventMass] at h
  exact h


end
end StatMech.FrontierD
