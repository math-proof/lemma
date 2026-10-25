/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripMassLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripFamilyMass.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits


namespace StatMech.Universality

open HexWalk Filter Topology

noncomputable section

def HexCSSideWalkAtWidth (T : ℕ) (hT : 0 < T) (ts : List ℤ) : Prop :=
  ∃ L, HexCSSideWalk T L hT ts

end
end StatMech.Universality
