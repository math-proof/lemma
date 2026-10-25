/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripGeometry.Part11
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCS_endpoint_normalized_dcs_identity
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hlaw : HexCSCanonicalWindingLaw T L hT)
    (hstart : HexCSStartReturnLaw T L hT) :
    let H := hexCSEndpointMirrorOrbitData T L hT hlocal hlaw hstart
    let Kc := hexCSDCSClassification T L hT hlocal hlaw hstart
    hexCl * H.dcsLam Kc + hexCt * H.dcsTau Kc + H.dcsUps Kc = 1 := by
  dsimp only
  exact HexEndpointMirrorOrbitData.normalized_dcs_identity _ _


end
end StatMech.Universality
