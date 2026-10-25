/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripInfiniteIdentity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripMassLimits.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2


namespace StatMech.Universality

open HexWalk Filter Topology

noncomputable section

noncomputable def hexCSInfiniteSideMass (v : ℕ) : ℝ :=
  hexCSPredicateMass
    (HexCSSideWalkAtWidth (v + 1) (Nat.succ_pos v))


noncomputable def hexCSInfiniteTopMass (v : ℕ) : ℝ :=
  hexCSPredicateMass
    (HexCSTopWalkAtWidth (v + 1) (Nat.succ_pos v))

end
end StatMech.Universality
