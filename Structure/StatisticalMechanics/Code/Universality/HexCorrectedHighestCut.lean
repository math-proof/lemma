/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
import Abbrev.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut


namespace StatMech.Universality

open HexWalk

noncomputable section

set_option maxHeartbeats 800000 in


structure HexCSHighestCut (T : ℕ) (hT : 1 ≤ T) where
  split : {ts : List ℤ // HexCSNewSideWalk T hT ts} →
    HexCSNextTopWalk T hT × HexCSNextTopWalk T hT
  split_injective : Function.Injective split
  length_add_one : ∀ d,
    (ofTurns hexAWStart 1 (split d).1.1).endpointNumVertices +
        (ofTurns hexAWStart 1 (split d).2.1).endpointNumVertices =
      (ofTurns hexAWStart 1 d.1).endpointNumVertices + 1

end
end StatMech.Universality
