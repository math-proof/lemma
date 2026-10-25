/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSingleStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexProjPhaseClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Def.StatisticalMechanics.Code.Universality.HexSingleStartPhaseRepair


namespace StatMech.Universality

open Complex

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexSingleStartPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexSingleStartPhaseData D P R)

@[simp] theorem toHalfStartRegionAssign_lam :
    H.toHalfStartRegionAssign.lam = H.lam := rfl

@[simp] theorem toHalfStartRegionAssign_taup :
    H.toHalfStartRegionAssign.taup = H.taup := rfl

@[simp] theorem toHalfStartRegionAssign_taum :
    H.toHalfStartRegionAssign.taum = H.taum := rfl

@[simp] theorem toHalfStartRegionAssign_ups :
    H.toHalfStartRegionAssign.ups = H.ups := rfl

@[simp] theorem toHalfStartRegionAssign_Fa :
    H.toHalfStartRegionAssign.Fa = H.Fa / 2 := rfl

end HexSingleStartPhaseData


theorem hexBdryAssign_identity_fa
    {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
    (hsub : P.interior ⊆ D.incidences)
    (A : HexRegionAssign D P R) :
    hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups = A.Fa := by
  have hraw := D.hexBoundaryRaw P hsub
  have hdecomp := A.toDecomp.boundarySum_eq
  rw [hraw] at hdecomp
  have hcast' :
      ((hexBdryCl * A.toDecomp.lam
          + hexBdryCt * (A.toDecomp.taup + A.toDecomp.taum)
          + A.toDecomp.ups : ℝ) : ℂ) - (A.toDecomp.Fa : ℂ) = 0 := by
    exact (mul_eq_zero.mp hdecomp.symm).resolve_left Complex.I_ne_zero
  have hcast :
      ((hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups : ℝ) : ℂ)
          - (A.Fa : ℂ) = 0 := by
    simpa only [HexRegionAssign.toDecomp, HexRegionAssign.toFamilyData,
      HexFamilyData.toDecomp] using hcast'
  have hreal :
      (hexBdryCl * A.lam + hexBdryCt * (A.taup + A.taum) + A.ups : ℝ)
          - A.Fa = 0 := by
    exact_mod_cast hcast
  linarith

namespace HexSingleStartPhaseData

variable {D : HexDomain V} {P : D.InteriorPairing} {R : HexRegion}
  (H : HexSingleStartPhaseData D P R)


theorem correctedInterface_identity_half
    (hsub : P.interior ⊆ D.incidences) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups = H.Fa / 2 := by
  have h := hexBdryAssign_identity_fa hsub H.toHalfStartRegionAssign
  exact h


theorem correctedInterface_identity_hexChi_half
    (hsub : P.interior ⊆ D.incidences) (hFa : H.Fa = hexChi) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups
      = hexChi / 2 := by
  calc
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups
        = H.Fa / 2 := H.correctedInterface_identity_half hsub
    _ = hexChi / 2 := by rw [hFa]


theorem correctedInterface_normalized_identity
    (hsub : P.interior ⊆ D.incidences) (hFa : H.Fa = hexChi) :
    hexBdryCl * ((2 * hexChi⁻¹) * H.lam)
      + hexBdryCt * ((2 * hexChi⁻¹) * (H.taup + H.taum))
      + (2 * hexChi⁻¹) * H.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have h := H.correctedInterface_identity_hexChi_half hsub hFa
  calc
    hexBdryCl * ((2 * hexChi⁻¹) * H.lam)
          + hexBdryCt * ((2 * hexChi⁻¹) * (H.taup + H.taum))
          + (2 * hexChi⁻¹) * H.ups
        = (2 * hexChi⁻¹) *
            (hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups) := by
              ring
    _ = (2 * hexChi⁻¹) * (hexChi / 2) := by rw [h]
    _ = 1 := by field_simp


theorem Fa_eq_boundaryData_Fa
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start) : H.Fa = B.Fa := by
  apply Complex.ofReal_injective
  calc
    (H.Fa : ℂ) = D.obs R.start := H.obsStart.symm
    _ = D.obs Rf.start := by rw [hstart]
    _ = (B.Fa : ℂ) := B.Fa_eq.symm


theorem Fa_eq_hexChi_of_boundaryData
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start) : H.Fa = hexChi :=
  (H.Fa_eq_boundaryData_Fa B hstart).trans B.Fa_eq_hexChi


theorem diagnostic_half_identity_of_boundaryData
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start) :
    hexBdryCl * H.lam + hexBdryCt * (H.taup + H.taum) + H.ups
      = hexChi / 2 :=
  H.correctedInterface_identity_hexChi_half B.interior_sub
    (H.Fa_eq_hexChi_of_boundaryData B hstart)


theorem boundaryData_identity_of_halfScaled_contours
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start)
    (hlam : H.lam = B.lam / 2)
    (htau : H.taup + H.taum = B.tau / 2)
    (hups : H.ups = B.ups / 2) :
    hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups = hexChi := by
  have h := H.diagnostic_half_identity_of_boundaryData B hstart
  rw [hlam, htau, hups] at h
  linarith


theorem normalized_boundaryData_identity_of_halfScaled_contours
    {Rf : HexFiniteRegion} {h0 : ℤ}
    (B : HexFiniteStripBoundaryData Rf h0 D P)
    (hstart : R.start = Rf.start)
    (hlam : H.lam = B.lam / 2)
    (htau : H.taup + H.taum = B.tau / 2)
    (hups : H.ups = B.ups / 2) :
    hexBdryCl * (hexChi⁻¹ * B.lam)
      + hexBdryCt * (hexChi⁻¹ * B.tau)
      + hexChi⁻¹ * B.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have h := H.boundaryData_identity_of_halfScaled_contours
    B hstart hlam htau hups
  calc
    hexBdryCl * (hexChi⁻¹ * B.lam)
          + hexBdryCt * (hexChi⁻¹ * B.tau)
          + hexChi⁻¹ * B.ups
        = hexChi⁻¹ *
            (hexBdryCl * B.lam + hexBdryCt * B.tau + B.ups) := by ring
    _ = hexChi⁻¹ * hexChi := by rw [h]
    _ = 1 := inv_mul_cancel₀ hchi

end HexSingleStartPhaseData

namespace HexFiniteStripBoundaryData


theorem obs_start_eq_hexChi
    {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
    {P : D.InteriorPairing} (B : HexFiniteStripBoundaryData R h0 D P) :
    D.obs R.start = (hexChi : ℂ) := by
  calc
    D.obs R.start = (B.Fa : ℂ) := B.Fa_eq.symm
    _ = (hexChi : ℂ) := by rw [B.Fa_eq_hexChi]

end HexFiniteStripBoundaryData
end StatMech.Universality
