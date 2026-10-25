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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorFiniteGraph.Part62
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_connectorForceTraceConfig_finiteEdge {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (tau : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : (rlc_connectorFiniteGraph gamma gamma').edgeSet) :
    rlc_connectorForceTraceConfig gamma gamma' tau e.1 = tau e.1 := by
  unfold rlc_connectorForceTraceConfig
  rw [if_neg]
  intro htrace
  induction heq : e.1 using Sym2.inductionOn with
  | _ x y =>
      have hefinite := e.2
      rw [heq] at hefinite htrace
      exact rlc_connectorFiniteGraph_adj_not_traceWiring gamma gamma'
        ((SimpleGraph.mem_edgeSet _).mp hefinite)
        ((SimpleGraph.mem_edgeSet _).mp
          (SimpleGraph.mem_edgeFinset.mp htrace))

theorem rlc_connectorVariableSourceEdge_map {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorPIMSVariableGraph gamma gamma').edgeSet) :
    (rlc_connectorVariableSourceEdge gamma gamma' e).1.map Subtype.val =
      rlc_pimsEdgeEquiv (e.1.map Subtype.val) := by
  change (rlc_connectorEdgeLift gamma gamma'
      (rlc_pimsEdgeEquiv (e.1.map Subtype.val))
      (rlc_connectorVariableEdge_preimage_mem_connector
        gamma gamma' e)).map Subtype.val = _
  exact rlc_connectorEdgeLift_map gamma gamma' _
    (rlc_connectorVariableEdge_preimage_mem_connector gamma gamma' e)

theorem rlc_connectorInnerSourceEdge_map {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (e : (rlc_connectorInnerGraph gamma gamma').edgeSet) :
    (rlc_connectorInnerSourceEdge gamma gamma' e).1.map Subtype.val =
      rlc_pimsEdgeEquiv
        ((rlc_connectorInnerEdgeToVariable gamma gamma' e).1.map
          Subtype.val) := by
  change (rlc_connectorVariableSourceEdge gamma gamma'
      (rlc_connectorInnerVariableEdgeEquiv gamma gamma' e)).1.map
        Subtype.val = _
  rw [show rlc_connectorInnerVariableEdgeEquiv gamma gamma' e =
      rlc_connectorInnerEdgeToVariable gamma gamma' e from rfl]
  exact rlc_connectorVariableSourceEdge_map gamma gamma' _


end
end StatMech.Universality
