/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripColumn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedColumnLength
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripIdentity.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

noncomputable def hexCSTopFiniteWeight
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : ℝ := by
  classical
  exact if HexCSTopWalk T L hT ts then
      hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices
    else 0

end
end StatMech.Universality
