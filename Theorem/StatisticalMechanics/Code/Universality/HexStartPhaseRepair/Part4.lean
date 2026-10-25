/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStartPhaseRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part4
import Def.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part3


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators

variable {V : Type*} [DecidableEq V]


namespace HexFiniteStripFourPhaseData

variable {R : HexFiniteRegion} {h0 : ℤ} {D : HexDomain V}
  {P : D.InteriorPairing} {C : HexFiniteStripBoundaryCore R h0 D P}
  {G : HexRegion} (H : HexFiniteStripFourPhaseData C G)

include H


@[simp] theorem toHalfRegionAssign_lam : H.toHalfRegionAssign.lam = C.lam / 2 := rfl

@[simp] theorem toHalfRegionAssign_taup : H.toHalfRegionAssign.taup = H.taup / 2 := rfl

@[simp] theorem toHalfRegionAssign_taum : H.toHalfRegionAssign.taum = H.taum / 2 := rfl

@[simp] theorem toHalfRegionAssign_ups : H.toHalfRegionAssign.ups = C.ups / 2 := rfl

@[simp] theorem toHalfRegionAssign_Fa : H.toHalfRegionAssign.Fa = C.Fa / 2 := rfl


theorem boundary_identity_fa :
    hexBdryCl * C.lam + hexBdryCt * (H.taup + H.taum) + C.ups = C.Fa := by
  have hraw : D.boundarySum P = 0 := D.hexBoundaryRaw P C.interior_sub
  have hdecomp := H.toHalfRegionAssign.toDecomp.boundarySum_eq
  rw [hraw] at hdecomp
  simp only [HexRegionAssign.toDecomp, HexRegionAssign.toFamilyData,
    HexFamilyData.toDecomp, toHalfRegionAssign] at hdecomp
  have hzero :
      ((hexBdryCl * (C.lam / 2)
          + hexBdryCt * (H.taup / 2 + H.taum / 2)
          + C.ups / 2 : ℝ) : ℂ) - ((C.Fa / 2 : ℝ) : ℂ) = 0 := by
    rcases mul_eq_zero.mp hdecomp.symm with hi | hz
    · exact (Complex.I_ne_zero hi).elim
    · exact hz
  have hreal :
      (hexBdryCl * (C.lam / 2)
          + hexBdryCt * (H.taup / 2 + H.taum / 2)
          + C.ups / 2 : ℝ) - C.Fa / 2 = 0 := by
    exact_mod_cast hzero
  linarith


theorem normalized_boundary_identity :
    hexBdryCl * (hexChi⁻¹ * C.lam)
      + hexBdryCt * (hexChi⁻¹ * C.tau)
      + hexChi⁻¹ * C.ups = 1 := by
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have hid := H.boundary_identity_fa
  rw [H.tau_eq, C.Fa_eq_hexChi] at hid
  calc
    hexBdryCl * (hexChi⁻¹ * C.lam)
          + hexBdryCt * (hexChi⁻¹ * C.tau)
          + hexChi⁻¹ * C.ups =
        hexChi⁻¹ *
          (hexBdryCl * C.lam + hexBdryCt * C.tau + C.ups) := by ring
    _ = hexChi⁻¹ * hexChi := by rw [hid]
    _ = 1 := inv_mul_cancel₀ hchi


theorem normalized_contour_boundary_identity :
    hexBdryCl *
        (hexChi⁻¹ *
          hexContourLambda R.inRegion R.start h0 C.sides hexChi)
      + hexBdryCt *
        (hexChi⁻¹ *
          (hexContourTauPlus R.inRegion R.start h0 C.sides hexChi
            + hexContourTauMinus R.inRegion R.start h0 C.sides hexChi))
      + hexChi⁻¹ *
          hexContourUpsilon R.inRegion R.start h0 C.sides hexChi = 1 := by
  rw [← C.lam_eq, ← C.tau_eq, ← C.ups_eq]
  exact H.normalized_boundary_identity

end HexFiniteStripFourPhaseData
end StatMech.Universality
