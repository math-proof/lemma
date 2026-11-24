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
public import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part13
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

@[simp] theorem rlc_connectorAmbientMixedConfig_connectorEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)} (he : e ∈ rlc_connectorEdges gamma gamma') :
    rlc_connectorAmbientMixedConfig gamma gamma' tau e =
      tau (rlc_connectorEdgeLift gamma gamma' e he) := by
  simp [rlc_connectorAmbientMixedConfig, he]

@[simp] theorem rlc_connectorAmbientMixedConfig_traceEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorAmbientMixedConfig gamma gamma' tau e = true := by
  have hnot : e ∉ rlc_connectorEdges gamma gamma' := by
    rcases Finset.mem_union.mp he with hright | hleft
    · exact Finset.disjoint_left.mp
        (rlc_rightPathEdges_disjoint_connector gamma gamma') hright
    · exact Finset.disjoint_left.mp
        (rlc_leftPathEdges_disjoint_connector gamma gamma') hleft
  simp [rlc_connectorAmbientMixedConfig, hnot, he]


end
end StatMech.Universality
