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
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part70
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def RlcConnectorPIMSContourArcSide {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {u x y : Site 2}
    (c : (faceBoundaryGraph (rlc_connectorReachSet gamma gamma'
      (rlc_connectorAmbientMixedConfig gamma gamma' tau))).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support) : Prop :=
  let eta := rlc_maskConfig (rlc_connectorEdges gamma gamma')
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  let hle := rlc_faceBoundaryGraph_le_openFaceDual gamma gamma'
    (rlc_connectorAmbientMixedConfig gamma gamma' tau)
  (∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_orderedContourArc c hx hy).mapLe hle)).edges,
      e ∈ rlc_connectorEdges gamma gamma') ∨
    ∀ e ∈ (rlc_dualReflectOpenWalk eta
      ((rlc_complementaryContourArc c hx hy).mapLe hle)).edges,
      e ∈ rlc_connectorEdges gamma gamma'


end
end StatMech.Universality
