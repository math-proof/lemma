/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSmallIncidenceEnumeration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexSmallIncidenceEnumeration.Part5


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


theorem hexSmallCell_boundary_identity_false :
    hexBdryCt * (hexChi ^ 2) + hexChi ^ 2 ≠ hexChi := by
  intro h
  have hchi : hexChi ≠ 0 := ne_of_gt hexChi_pos
  have hfac : hexChi * ((hexBdryCt + 1) * hexChi - 1) = 0 := by
    nlinarith
  have hlin : (hexBdryCt + 1) * hexChi = 1 := by
    rcases mul_eq_zero.mp hfac with hz | hz
    · exact (hchi hz).elim
    · linarith
  rw [hexChi_eq_sqrt] at hlin
  unfold hexBdryCt at hlin
  rw [Real.cos_pi_div_four] at hlin
  have hspos : 0 < Real.sqrt (2 + Real.sqrt 2) := by positivity
  field_simp [ne_of_gt hspos] at hlin
  have hs2 : Real.sqrt (2 + Real.sqrt 2) ^ 2 = 2 + Real.sqrt 2 :=
    Real.sq_sqrt (by positivity)
  have hr2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith


theorem hexSmallCell_noFourPhaseData (a : ℂ) (h0 : ℤ) (G : HexRegion) :
    ¬ Nonempty (HexFiniteStripFourPhaseData
      (hexSmallCellBoundaryCore a h0) G) := by
  rintro ⟨H⟩
  have hid := H.boundary_identity_fa
  rw [H.tau_eq] at hid
  change hexBdryCl * 0 + hexBdryCt * (hexChi ^ 2) + hexChi ^ 2 =
    hexChi at hid
  exact hexSmallCell_boundary_identity_false (by simpa using hid)


theorem hexSmallCell_noFourPhaseLiftData (a : ℂ) (G : HexRegion) :
    ¬ Nonempty (HexFiniteStripFourPhaseLiftData
      (hexSmallCellCoreOrientation a) G) := by
  rintro ⟨Q⟩
  exact hexSmallCell_noFourPhaseData a 1 G ⟨Q.toFourPhaseData⟩


theorem hexSmallCell_noLegacyBoundaryData (a : ℂ) (h0 : ℤ) :
    ¬ ∃ B : HexFiniteStripBoundaryData (hexVBCRegion a h0) h0
        (hexUncondDomain a h0) (hexUncondPairing a h0),
      B.sides = hexSmallCellSides a h0 := by
  rintro ⟨B, hsides⟩
  have hlam : B.lam = 0 := by
    calc
      B.lam = hexContourLambda (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 B.sides hexChi := B.lam_eq
      _ = hexContourSum (hexVBCRegion a h0).inRegion a h0 ∅ hexChi := by
        rw [hsides]
        rfl
      _ = 0 := hexContourSum_empty _ _ _ _
  have htau : B.tau = hexChi ^ 2 := by
    calc
      B.tau = hexContourTauPlus (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 B.sides hexChi
          + hexContourTauMinus (hexVBCRegion a h0).inRegion
            (hexVBCRegion a h0).start h0 B.sides hexChi := B.tau_eq
      _ = hexContourSum (hexVBCRegion a h0).inRegion a h0
            ({hexConcreteQ a h0} : Set ℂ) hexChi
          + hexContourSum (hexVBCRegion a h0).inRegion a h0 ∅ hexChi := by
        rw [hsides]
        rfl
      _ = hexChi ^ 2 := by
        rw [hexVBC_contourSum_singleton_q, hexContourSum_empty, add_zero]
  have hups : B.ups = hexChi ^ 2 := by
    calc
      B.ups = hexContourUpsilon (hexVBCRegion a h0).inRegion
          (hexVBCRegion a h0).start h0 B.sides hexChi := B.ups_eq
      _ = hexContourSum (hexVBCRegion a h0).inRegion a h0
          ({hexConcreteR a h0} : Set ℂ) hexChi := by
        rw [hsides]
        rfl
      _ = hexChi ^ 2 := hexVBC_contourSum_singleton_r a h0 hexChi
  have hFa : B.Fa = hexChi := B.Fa_eq_hexChi
  have hid := B.boundary_identity_fa
  rw [hlam, htau, hups, hFa] at hid
  exact hexSmallCell_boundary_identity_false (by simpa using hid)

end StatMech.Universality
