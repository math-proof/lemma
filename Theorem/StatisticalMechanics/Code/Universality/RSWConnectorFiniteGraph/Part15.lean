/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part18
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

@[simp] theorem rlc_connectorPIMSCollaredParameter_of_preimage_connector
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSCollaredParameter gamma gamma' p e = p := by
  simp [rlc_connectorPIMSCollaredParameter, he]

@[simp] theorem rlc_connectorPIMSCollaredParameter_of_preimage_exterior
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSCollaredParameter gamma gamma' p e = 0 := by
  simp [rlc_connectorPIMSCollaredParameter, he]

@[simp] theorem rlc_connectorPIMSCollaredParameter_of_preimage_trace
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (p : Real) (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSCollaredParameter gamma gamma' p e = 0 := by
  apply rlc_connectorPIMSCollaredParameter_of_preimage_exterior
  rcases Finset.mem_union.mp he with hright | hleft
  · exact Finset.disjoint_left.mp
      (rlc_rightPathEdges_disjoint_connector gamma gamma') hright
  · exact Finset.disjoint_left.mp
      (rlc_leftPathEdges_disjoint_connector gamma gamma') hleft


end
end StatMech.Universality
