/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripFamilyMass.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMasses
import Instance.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

noncomputable def hexCSClassWalkMass
    (T L : ℕ) (hT : 0 < T) (cls : HexPairedBoundaryClass) : ℝ :=
  by
    classical
    exact ∑' ts : List ℤ,
      if HexCSClassWalk T L hT cls ts then
        hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices
      else 0

end
end StatMech.Universality
