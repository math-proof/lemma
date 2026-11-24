module
public import Theorem.StatisticalMechanics.Code.Universality.RSWGapSymmetry.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalTraceContact
public import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
public import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreDomination.Part13
public import Theorem.StatisticalMechanics.Code.FK.WeightedParameterMonotoneClosed
public import Theorem.StatisticalMechanics.Code.FrontierD.FKBoundarySingleMerge
public import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part40
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorFiniteGraph.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable def rlc_connectorVariableSourceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet →
      (rlc_connectorFiniteGraph gamma gamma').edgeSet :=
  fun e =>
    let source := rlc_pimsEdgeEquiv (e.1.map Subtype.val)
    let hsource : source ∈ rlc_connectorEdges gamma gamma' :=
      rlc_connectorVariableEdge_preimage_mem_connector gamma gamma' e
    ⟨rlc_connectorEdgeLift gamma gamma' source hsource,
      rlc_connectorEdgeLift_mem_finiteGraph gamma gamma' source hsource
        (rlc_pimsEdgeEquiv_mem_latticeEdge
          (rlc_connectorVariableEdge_map_mem_lattice gamma gamma' e))⟩

end
end StatMech.Universality
