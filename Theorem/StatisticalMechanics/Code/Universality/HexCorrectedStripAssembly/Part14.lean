/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part15


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCS_dcsLam_eq_A
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    H.dcsLam Kc = hexCSA T L hT := by
  rfl

theorem hexCS_dcsTau_eq_E
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    H.dcsTau Kc = hexCSE T L hT := by
  rfl

theorem hexCS_dcsUps_eq_B
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    H.dcsUps Kc = hexCSB T L hT := by
  rfl


theorem hexCS_finite_strip_identity
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    hexCl * hexCSA T L hT + hexCt * hexCSE T L hT +
      hexCSB T L hT = 1 := by
  have h := hexCS_endpoint_normalized_dcs_identity
    T L hT hlocal hlaw hstart
  dsimp only at h
  rw [hexCS_dcsLam_eq_A T L hT hlocal hlaw hstart,
    hexCS_dcsTau_eq_E T L hT hlocal hlaw hstart,
    hexCS_dcsUps_eq_B T L hT hlocal hlaw hstart] at h
  exact h

theorem hexCS_boundary_masses_nonneg
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    0 ≤ hexCSA T L hT ∧ 0 ≤ hexCSE T L hT ∧
      0 ≤ hexCSB T L hT := by
  let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
  let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
  have hnonneg : ∀ i, 0 ≤ (H.pairs i).mass := by
    intro i
    exact hexCSBoundaryPair_mass_nonneg T L hT hlocal hlaw i
  have h := H.dcs_values_nonneg Kc hnonneg
  simpa [H, Kc, hexCS_dcsLam_eq_A, hexCS_dcsTau_eq_E,
    hexCS_dcsUps_eq_B] using h

end
end StatMech.Universality
