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
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part73
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

def RlcConnectorPIMSActualSelectedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y),
    x ∈ rlc_pathVertices gamma.1 ∧
      y ∈ rlc_pathVertices gamma'.1 ∧
      (∀ z ∈ c.support,
        z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))) ∧
      (∀ e ∈ c.edges, e ∈ rlc_connectorEdges gamma gamma') ∧
      ∀ e ∈ c.edges,
        RlcConnectorPIMSSourceOpenCase gamma gamma' tau e


def RlcConnectorPIMSSupportedArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (c : (openSubgraph 2 (rlc_dualReflectConfig
      (rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)))).Walk x y),
    x ∈ rlc_pathVertices gamma.1 ∧
      y ∈ rlc_pathVertices gamma'.1 ∧
      (∀ z ∈ c.support,
        z ∈ (rect (-2 * n) (2 * n) (-n) n : Set (Site 2))) ∧
      (∀ e ∈ c.edges, e ∈ rlc_connectorEdges gamma gamma') ∧
      ∀ e ∈ c.edges, rlc_pimsEdgeEquiv e ∉
        rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1


end
end StatMech.Universality
