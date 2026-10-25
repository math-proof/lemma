/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCyclicAtomSupport
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointPieceRigidity
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointTripletOrbit
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripStartReturn
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLocal.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

structure HexCSTerminalPairCertificate
    (T L : ℕ) (hT : 0 < T) (c : HexAWCoord) where
  pair : HexEndpointCyclicLoopPair
    (hexCSFiniteRegion T L hT).inRegion hexAWStart 1
    (hexAWPos c) (hexAWMid c 0 - hexAWPos c)
  stem : hexInfra_midAccum hexAWStart 1 pair.base +
    halfStep (hexInfra_headAccum 1 pair.base) = hexAWPos c
  count : ∀ u ∈ pair.piece,
    specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) u = 3

end
end StatMech.Universality
