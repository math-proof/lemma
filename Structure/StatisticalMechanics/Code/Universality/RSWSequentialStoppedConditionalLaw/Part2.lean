/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSequentialStoppedConditionalLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedExplorationBridge
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassCapstone.Part2
import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part10
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

structure RlcBookFaithfulStratumReplacement {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (delta : RlcRightDiagonalPath n) (delta' : RlcLeftDiagonalPath n) : Prop where
  faithful : RlcBookFaithfulTracePair delta delta'
  right_edges : rlc_pathEdges delta.1 ⊆ rlc_pathEdges gamma.1
  left_edges : rlc_pathEdges delta'.1 ⊆ rlc_pathEdges gamma'.1
  right_explored : rlc_rightExploredVertices delta =
    rlc_rightExploredVertices gamma
  left_explored : rlc_leftExploredVertices delta' =
    rlc_leftExploredVertices gamma'


end
end StatMech.Universality
