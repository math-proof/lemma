/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingOneThermodynamicBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneResidualLower
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorThermodynamicBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectUnitLeftBarrier.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingOneThermodynamicBridge
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

structure FKRectWindingOneSource (R : FKRectTorus) (q : Real) where
  leftRight : Nat
  cut : Nat
  sep : leftRight < cut
  left : leftRight + 1 < R.width
  gap : R.EdgeIndex
  gap_mem : gap ∈ fkRectHorizontalCutEdges R
  x : Fin R.width
  x_right : cut <= x.val
  chosen : fkRectVerticalSeamEdgeAt R x ≠ gap
  pairs : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
    FKRectRightStripBandVertex R cut 1 (R.height - 1))
  chain_spans :
    FKRectRightBandConnectionChainSpans R cut x x_right pairs
  pair_reachable : ∀ xy ∈ pairs,
    (fkRectInducedGraph R
      (fkRectRightStripBand R cut 1 (R.height - 1))).Reachable xy.1 xy.2
  barrierConfiguration : R.Configuration
  barrier_mem : barrierConfiguration ∈
    fkRectSourceLeftBarrier R leftRight gap


end
end StatMech.FrontierD
