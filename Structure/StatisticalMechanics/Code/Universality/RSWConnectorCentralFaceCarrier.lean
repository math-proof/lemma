/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part6
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcBookPositionedTracePair {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop where
  exposed_disjoint : Disjoint (rlc_pathVertices gamma.1)
    (rlc_pathVertices gamma'.1)
  right_axis_strict : (gamma.1.1 : Site 2) 1 < 0
  left_axis_strict : 0 < (gamma'.1.2.1 : Site 2) 1


structure RlcBookFaithfulTracePair {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop
    extends RlcBookPositionedTracePair gamma gamma' where
  right_axis_unique : forall {z : Site 2},
    z ∈ rlc_pathVertices gamma.1 -> z 0 = 0 ->
      z = (gamma.1.1 : Site 2)
  left_axis_unique : forall {z : Site 2},
    z ∈ rlc_pathVertices gamma'.1 -> z 0 = 0 ->
      z = (gamma'.1.2.1 : Site 2)


structure RlcBookFaithfulExtremalTracePair {n : Int}
    (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) : Prop
    extends RlcBookFaithfulTracePair gamma gamma' where
  extremal_realizable :
    (rlc_extremalPairCandidate (gamma, gamma')).Nonempty


end
end StatMech.Universality
