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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part17
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorPIMSCollaredReflectedConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e =
      !(rlc_connectorAmbientCollaredConfig gamma gamma' tau
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_connectorPIMSCollaredReflectedConfig
    rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims
    (rlc_connectorAmbientCollaredConfig gamma gamma' tau)
    (e.map Subtype.val)

theorem rlc_connectorPIMSCollaredReflectedConfig_of_preimage_connector
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_connectorEdges gamma gamma') :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e =
      !(tau (rlc_connectorEdgeLift gamma gamma'
        (rlc_pimsEdgeEquiv (e.map Subtype.val)) he)) := by
  rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
    rlc_connectorAmbientCollaredConfig_connectorEdge gamma gamma' tau he]

theorem rlc_connectorPIMSCollaredReflectedConfig_of_preimage_trace
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (he : rlc_pimsEdgeEquiv (e.map Subtype.val) ∈
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = false := by
  rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
    rlc_connectorAmbientCollaredConfig_traceEdge gamma gamma' tau he]
  rfl


theorem rlc_connectorPIMSCollaredReflectedConfig_of_preimage_exterior
    {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n))
    (htarget : e.map Subtype.val ∈ rlc_connectorEdges gamma gamma')
    (hG : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_connectorEdges gamma gamma')
    (htrace : rlc_pimsEdgeEquiv (e.map Subtype.val) ∉
      rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorPIMSCollaredReflectedConfig gamma gamma' tau e = false := by
  have hcollar := rlc_pimsEdgeEquiv_mem_connectorPIMSExteriorPreimages
    gamma gamma' htarget hG htrace
  rw [rlc_connectorPIMSCollaredReflectedConfig_apply,
    rlc_connectorAmbientCollaredConfig_collarEdge gamma gamma' tau hcollar]
  rfl


end
end StatMech.Universality
