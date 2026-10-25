/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusWindingCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusAllChargeReduction
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurningFiber.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectMedialLoopTurnClassification.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerDefectClassification
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingCountBridge


namespace StatMech.FrontierD

noncomputable section

theorem fkRectFixedChargeTilt_pos_of_windingNumber_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) (lam : Real)
    (omega : R.Configuration) (r : Nat)
    (hr : r ≤ R.medialTorus.width / 2)
    (hU : fkRectUnorientedVerticalWindingNumber R omega = r) :
    0 < fkRectFixedChargeTilt R q lam r hr omega := by
  obtain ⟨arrows, hweight, hflux⟩ :=
    exists_positive_weight_verticalFlux_eq_neg_two_mul_half lam
      (fkRectConfigurationToMedialPairing R omega)
  have hU' :
      ((fkMedialUnorientedVerticalWindingTotal
          (fkRectConfigurationToMedialPairing R omega) / 2 : Nat) : Int) =
        (r : Int) := by
    exact_mod_cast hU
  have hflux' : fkOrientedLoopVerticalFlux R.medialTorus arrows =
      -(2 * (r : Int)) := by
    rw [hU'] at hflux
    exact hflux
  rw [fkRectFixedChargeTilt_eq_verticalFluxTilt]
  unfold fkRectVerticalFluxTilt
  apply div_pos
  · apply Finset.sum_pos'
    · intro a ha
      split
      · exact fkOrientedLoopPairingWeight_nonneg lam
          (fkRectConfigurationToMedialPairing R omega) a
      · norm_num
    · refine ⟨arrows, Finset.mem_univ _, ?_⟩
      rw [if_pos hflux']
      exact hweight
  · exact fkRectCriticalReducedWeight_pos R hq omega


theorem fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus) (r : Nat)
    (hweight : fkRectOrientedLoopWeight R lam omega arrows ≠ 0)
    (hflux : fkOrientedLoopVerticalFlux R.medialTorus arrows =
      -(2 * (r : Int))) :
    r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
  have hcompat : ∀ v,
      fkLoopPairingCompatible
        (fkRectConfigurationToMedialPairing R omega v) arrows v := by
    exact (fkOrientedLoopPairingWeight_ne_zero_iff_compatible
      lam (fkRectConfigurationToMedialPairing R omega) arrows).1 hweight
  exact le_half_unorientedWindingTotal_of_verticalFlux_eq_neg_two_mul
    (fkRectConfigurationToMedialPairing R omega) arrows hcompat r hflux


theorem fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2)
    (hweight : fkRectOrientedLoopWeight R lam omega arrows ≠ 0)
    (hsector : sixVertexUpCount
        (svTorusVerticalRows R.medialTorus arrows
          (svFinLast R.medialTorus.height_pos)) =
      R.medialTorus.width / 2 - r) :
    r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
  apply fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux
    R lam omega arrows r hweight
  exact fkOrientedLoopVerticalFlux_eq_neg_two_mul_of_fixedCharge
    R.medialTorus arrows r hr hsector


theorem fkRectVerticalFluxSummand_ne_zero_imp_windingNumber_ge
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus) (r : Nat)
    (hterm : (if fkOrientedLoopVerticalFlux R.medialTorus arrows =
          -(2 * (r : Int)) then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) ≠ 0) :
    r ≤ fkRectUnorientedVerticalWindingNumber R omega := by
  by_cases hflux : fkOrientedLoopVerticalFlux R.medialTorus arrows =
      -(2 * (r : Int))
  · apply fkRectUnorientedVerticalWindingNumber_ge_of_weight_ne_zero_of_flux
      R lam omega arrows r
    · simpa [hflux] using hterm
    · exact hflux
  · simp [hflux] at hterm


theorem fkRectFixedChargeSummand_le_windingRestrictedSummand
    (R : FKRectTorus) (lam : Real) (omega : R.Configuration)
    (arrows : SixVertexArrows R.medialTorus)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    (if sixVertexUpCount
          (svTorusVerticalRows R.medialTorus arrows
            (svFinLast R.medialTorus.height_pos)) =
          R.medialTorus.width / 2 - r then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0) ≤
      if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
        fkRectOrientedLoopWeight R lam omega arrows
      else 0 := by
  by_cases hsector : sixVertexUpCount
      (svTorusVerticalRows R.medialTorus arrows
        (svFinLast R.medialTorus.height_pos)) =
      R.medialTorus.width / 2 - r
  · rw [if_pos hsector]
    by_cases hweight : fkRectOrientedLoopWeight R lam omega arrows = 0
    · simp [hweight]
    · have hU := fkRectUnorientedVerticalWindingNumber_ge_of_fixedCharge
        R lam omega arrows r hr hweight hsector
      rw [if_pos hU]
  · rw [if_neg hsector]
    by_cases hU : r ≤ fkRectUnorientedVerticalWindingNumber R omega
    · rw [if_pos hU]
      exact fkOrientedLoopPairingWeight_nonneg lam
        (fkRectConfigurationToMedialPairing R omega) arrows
    · rw [if_neg hU]


theorem fkRectOrientedLoopFixedChargePartitionSum_le_windingRestricted
    (R : FKRectTorus) (lam : Real)
    (r : Nat) (hr : r ≤ R.medialTorus.width / 2) :
    fkRectOrientedLoopSectorPartitionSum R
        (fkRectFixedChargeSector R r hr) lam ≤
      ∑ omega : R.Configuration,
        if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          ∑ arrows : SixVertexArrows R.medialTorus,
            fkRectOrientedLoopWeight R lam omega arrows
        else 0 := by
  unfold fkRectOrientedLoopSectorPartitionSum fkRectFixedChargeSector
  apply Finset.sum_le_sum
  intro omega homega
  calc
    (∑ arrows : SixVertexArrows R.medialTorus,
        if sixVertexUpCount
            (svTorusVerticalRows R.medialTorus arrows
              (svFinLast R.medialTorus.height_pos)) =
            R.medialTorus.width / 2 - r then
          fkRectOrientedLoopWeight R lam omega arrows
        else 0) ≤
        ∑ arrows : SixVertexArrows R.medialTorus,
          if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
            fkRectOrientedLoopWeight R lam omega arrows
          else 0 := by
      apply Finset.sum_le_sum
      intro arrows harrows
      exact fkRectFixedChargeSummand_le_windingRestrictedSummand
        R lam omega arrows r hr
    _ = if r ≤ fkRectUnorientedVerticalWindingNumber R omega then
          ∑ arrows : SixVertexArrows R.medialTorus,
            fkRectOrientedLoopWeight R lam omega arrows
        else 0 := by
      split <;> simp_all


end
end StatMech.FrontierD
