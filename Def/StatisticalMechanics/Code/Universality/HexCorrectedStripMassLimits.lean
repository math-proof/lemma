/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2


namespace StatMech.Universality

open HexWalk Filter Topology

noncomputable section

noncomputable def hexCSPredicateWeight
    (P : List ℤ → Prop) (ts : List ℤ) : ℝ := by
  classical
  exact if P ts then
    hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices else 0

noncomputable def hexCSPredicateMass (P : List ℤ → Prop) : ℝ :=
  ∑' ts : List ℤ, hexCSPredicateWeight P ts

end
end StatMech.Universality
