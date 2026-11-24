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
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part69
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

def RlcConnectorPIMSBoundaryArc {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ (x y : Site 2)
    (a : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk x y),
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
      rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
      let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
        (rlc_connectorAmbientMixedConfig gamma gamma' tau)
      ∀ e ∈ (rlc_dualReflectOpenWalk eta (a.mapLe hle)).edges,
        e ∈ rlc_connectorEdges gamma gamma'


def RlcConnectorPIMSFilledBoundaryContacts {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∃ x y : Site 2,
    x ∈ (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).support ∧
    y ∈ (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).support ∧
    rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
    rlc_dualReflect y ∈ rlc_pathVertices gamma'.1


def RlcConnectorPIMSFilledBoundaryTargetSupported {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n))) : Prop :=
  ∀ {f g : Site 2},
    (faceBoundaryGraph (rlc_connectorFilledReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Adj f g →
    s(rlc_dualReflect f, rlc_dualReflect g) ∈
      rlc_connectorEdges gamma gamma'


def rlc_traceSplitCounterexampleFiniteAllClosed :
    ConfigSpace (Sym2 (RlcConnectorVertex 1)) := fun _ => false


end
end StatMech.Universality
